#!/usr/bin/env python3
import os, json, math, csv, time, hashlib
from pathlib import Path
import numpy as np, torchfile

root   = Path('.').resolve()
ls3d   = Path(os.environ.get('LS3DW_HOME','LS3D-W')).resolve()
stamp  = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
runout = root/'.tau_ledger'/'ls3dw_runs'/stamp
runout.mkdir(parents=True, exist_ok=True)
census_out = root/'.tau_ledger'/'census'/'census_full.tsv'
census_out.parent.mkdir(parents=True, exist_ok=True)

SYM_NORM_MAX = float(os.environ.get('TAU_SYM_NORM_MAX','0.02'))   # symmetry_rms / IOD
CONV_MIN     = float(os.environ.get('TAU_CONV_MIN','165.0'))      # 68-pt convexity
MAX_FILES    = int(os.environ['TAU_MAX_FILES']) if os.environ.get('TAU_MAX_FILES') else None

def sha256_canon(obj):
    b = json.dumps(obj, sort_keys=True, separators=(",",":")).encode("utf-8")
    return hashlib.sha256(b).hexdigest()

def np_points(arr):
    A = np.asarray(arr, float)
    if A.ndim == 1:
        n=A.size
        if n%3==0: A=A.reshape(-1,3)
        elif n%2==0: A=np.c_[A.reshape(-1,2), np.zeros((n//2,1))]
        else: return None
    if A.shape[0] in (2,3) and A.shape[1] not in (2,3): A=A.T
    if A.shape[1]==2: A=np.c_[A, np.zeros((A.shape[0],1))]
    if A.shape[1]!=3: return None
    return A

def extract_points_t7(t7):
    if isinstance(t7, dict):
        for k in ('pts_3d','pts3d','landmarks_3D','pts','points','landmarks'):
            if k in t7:
                P = np_points(t7[k]); 
                if P is not None and P.shape[0] >= 60: return P
        for v in t7.values():
            P = np_points(v); 
            if P is not None and P.shape[0] >= 60: return P
    return np_points(t7)

def pca_axes(P):
    C = P.mean(axis=0); Q=P-C
    S = (Q.T @ Q) / max(P.shape[0]-1,1)
    w,V = np.linalg.eigh(S)
    return C, V[:,2], V[:,1], V[:,0]

def symmetry_metrics(P):
    C, n, *_ = pca_axes(P)
    n = n/(np.linalg.norm(n)+1e-12)
    d = (P - C) @ n
    rms = float(np.sqrt((d*d).mean()))
    # normalize by IOD (eye corners 36,45 zero-based); fallback to bbox diag
    if P.shape[0]>45:
        iod = float(np.linalg.norm(P[45,:2]-P[36,:2]))
        norm = rms/(iod+1e-9)
    else:
        xy = P[:,:2]; diag = float(np.hypot(xy[:,0].ptp(), xy[:,1].ptp()))
        norm = rms/(diag+1e-9)
    return rms, norm

def angle_deg(A,B,C):
    u=A-B; v=C-B
    nu=float(np.linalg.norm(u)); nv=float(np.linalg.norm(v))
    if nu<1e-12 or nv<1e-12: return None
    x=float((u@v)/(nu*nv)); x=max(-1.0,min(1.0,x))
    return float(math.degrees(math.acos(x)))

def convexity_68(P):
    i_brow, i_nose, i_chin = 27, 33, 8
    if P.shape[0] <= 33: return None
    return angle_deg(P[i_brow], P[i_nose], P[i_chin])

def make_trace(P, rel_id, sym_rms, sym_norm, conv):
    t = {
        "face_id": rel_id,
        "landmarks_68x3": P.tolist(),
        "symmetry_rms": sym_rms,
        "symmetry_rms_norm": sym_norm,
        "convexity_deg": conv,
        "face_timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "face_sequence_number": 0
    }
    t["face_signature"] = sha256_canon(t)
    return t

scanned=kept=0
rows=[]
print(f"[t7-norm] scanning {ls3d} sym_norm<= {SYM_NORM_MAX} conv>= {CONV_MIN} max={MAX_FILES or 'all'}", flush=True)
for i,p in enumerate(ls3d.rglob('*.t7')):
    if MAX_FILES and i>=MAX_FILES: break
    if i % 200 == 0 and i>0: print(f"[t7-norm] visited={i} kept={kept}", flush=True)
    scanned += 1
    try: obj = torchfile.load(str(p))
    except Exception: continue
    P = extract_points_t7(obj)
    if P is None or P.shape[0]<60 or P.shape[1]!=3: continue
    sym_rms, sym_norm = symmetry_metrics(P)
    conv = convexity_68(P)
    if sym_rms is None or sym_norm is None or conv is None: continue
    if not (sym_norm <= SYM_NORM_MAX and conv >= CONV_MIN): continue
    kept += 1
    hrel = p.relative_to(ls3d).as_posix()
    t = make_trace(P, hrel, sym_rms, sym_norm, conv)
    h = t["face_signature"]
    d = (root/'.tau_ledger'/'ls3dw_runs'/stamp/h)
    d.mkdir(parents=True, exist_ok=True)
    (d/'face_trace.json').write_text(json.dumps(t, sort_keys=True, separators=(",",":")), encoding='utf-8')
    rows.append([h, t["convexity_deg"], t["symmetry_rms_norm"], None, "unknown", str((d/'face_trace.json').relative_to(root))])

# write census (normalized sym used in column)
with open(census_out,'w',encoding='utf-8',newline='') as f:
    wr=csv.writer(f,delimiter='\t')
    wr.writerow(['hash','convexity_deg','symmetry_rms_norm','confidence','tier','source_path'])
    for r in rows: wr.writerow(r)

print(f"[t7-norm] DONE scanned={scanned} admitted={kept} run_dir={runout}", flush=True)
print(f"[census] wrote {census_out} rows={len(rows)}", flush=True)
