#!/usr/bin/env python3
import os, json, math, csv, time, hashlib, sys
from pathlib import Path
import numpy as np
import torchfile

root   = Path('.').resolve()
ls3d   = Path(os.environ.get('LS3DW_HOME','LS3D-W')).resolve()
stamp  = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
runout = root/'.tau_ledger'/'ls3dw_runs'/stamp
runout.mkdir(parents=True, exist_ok=True)
census_out = root/'.tau_ledger'/'census'/'census_full.tsv'
census_out.parent.mkdir(parents=True, exist_ok=True)

SYM_MAX   = float(os.environ.get('TAU_SYM_MAX', '0.004'))
CONV_MIN  = float(os.environ.get('TAU_CONV_MIN','177.0'))
MAX_FILES = int(os.environ['TAU_MAX_FILES']) if os.environ.get('TAU_MAX_FILES') else None

cfg_path = root/'.tau_ledger'/'census'/'face_metrics_config.json'
try:
    CFG = json.loads(cfg_path.read_text(encoding='utf-8'))
except Exception:
    CFG = {}

def sha256_canon(obj):
    b = json.dumps(obj, sort_keys=True, separators=(",",":")).encode("utf-8")
    return hashlib.sha256(b).hexdigest()

def np_points(arr):
    A = np.asarray(arr, dtype=float)
    if A.ndim == 1:
        n = A.size
        if n % 3 == 0: A = A.reshape(-1,3)
        elif n % 2 == 0: A = np.c_[A.reshape(-1,2), np.zeros((n//2,1))]
        else: return None
    if A.shape[0] in (2,3) and A.shape[1] not in (2,3):
        A = A.T
    if A.shape[1] == 2:
        A = np.c_[A, np.zeros((A.shape[0],1))]
    if A.shape[1] != 3: return None
    return A

def extract_points_t7(t7):
    if isinstance(t7, dict):
        for k in ('pts_3d','pts3d','landmarks_3D','pts','points','landmarks'):
            if k in t7:
                P = np_points(t7[k])
                if P is not None and P.shape[0] >= 60: return P
        for v in t7.values():
            P = np_points(v)
            if P is not None and P.shape[0] >= 60: return P
    return np_points(t7)

def pca_axes(P):
    C = P.mean(axis=0)
    Q = P - C
    S = (Q.T @ Q) / max(P.shape[0]-1, 1)
    w,V = np.linalg.eigh(S)  # ascending
    pc1,pc2,pc3 = V[:,2], V[:,1], V[:,0]
    return C, pc1, pc2, pc3

def symmetry_rms(P):
    C, n, _, _ = pca_axes(P)
    n = n / (np.linalg.norm(n) + 1e-12)
    d = (P - C) @ n
    return float(np.sqrt((d*d).mean()))

def angle_deg(A,B,C):
    u = A-B; v = C-B
    nu = float(np.linalg.norm(u)); nv = float(np.linalg.norm(v))
    if nu < 1e-12 or nv < 1e-12: return None
    x = float((u @ v) / (nu*nv)); x = max(-1.0, min(1.0, x))
    return float(math.degrees(math.acos(x)))

def convexity_from_cfg(P):
    try:
        g = P[int(CFG['glabella'])]; s = P[int(CFG['subnasale'])]; p = P[int(CFG['pogonion'])]
        a = angle_deg(g, s, p)
        return (None if a is None else float(a)), 'config'
    except Exception:
        return None, 'none'

def convexity_heuristic(P):
    C, pc1, pc2, pc3 = pca_axes(P)
    U = np.stack([pc1,pc2,pc3], axis=1)
    L = (P - C) @ U
    i_brow = int(np.argmax(L[:,1]))
    i_chin = int(np.argmin(L[:,1]))
    i_nose = int(np.argmax(L[:,2]))
    a = angle_deg(P[i_brow], P[i_nose], P[i_chin])
    return (None if a is None else float(a)), 'heuristic'

def make_trace(P, rel_id):
    t = {
        "face_id": rel_id,
        "face_landmarks_468x3": P.tolist(),  # contains 68x3 here
        "face_timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "face_sequence_number": 0
    }
    try: t["symmetry_rms"] = symmetry_rms(P)
    except Exception: pass
    a, src = convexity_from_cfg(P)
    if a is None:
        try: a, src = convexity_heuristic(P)
        except Exception: a, src = None, 'none'
    if a is not None:
        t["convexity_deg"] = a
        t["convexity_source"] = src
    t["face_signature"] = sha256_canon(t)
    return t

scanned = kept = 0
rows = []
print(f"[t7-sweep] scanning {ls3d}  sym<= {SYM_MAX}  conv>= {CONV_MIN}  max={MAX_FILES or 'all'}", flush=True)
for i, p in enumerate(ls3d.rglob('*.t7')):
    if MAX_FILES and i >= MAX_FILES: break
    if i % 200 == 0 and i > 0:
        print(f"[t7-sweep] visited={i} kept={kept}", flush=True)
    scanned += 1
    try:
        obj = torchfile.load(str(p))
    except Exception:
        continue
    P = extract_points_t7(obj)
    if P is None or P.shape[0] < 60 or P.shape[1] != 3:
        continue
    t = make_trace(P, rel_id=p.relative_to(ls3d).as_posix())
    sym = t.get("symmetry_rms"); conv = t.get("convexity_deg")
    if sym is None or conv is None: 
        continue
    if not (sym <= SYM_MAX and conv >= CONV_MIN):
        continue
    kept += 1
    h = t["face_signature"]
    d = runout/h; d.mkdir(parents=True, exist_ok=True)
    (d/'face_trace.json').write_text(json.dumps(t, sort_keys=True, separators=(",",":")), encoding='utf-8')
    rows.append([h, conv, sym, None, "unknown", str((d/'face_trace.json').relative_to(root))])

# dedupe by hash
seen = {}
for r in rows:
    if r[0] not in seen: seen[r[0]] = r

with census_out.open('w', encoding='utf-8', newline='') as f:
    wr = csv.writer(f, delimiter='\t')
    wr.writerow(['hash','convexity_deg','symmetry_rms','confidence','tier','source_path'])
    for r in seen.values():
        wr.writerow(r)

print(f"[t7-sweep] DONE scanned={scanned} admitted={kept} run_dir={runout}", flush=True)
print(f"[census] wrote {census_out} rows={len(seen)}", flush=True)
