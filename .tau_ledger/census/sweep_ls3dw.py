#!/usr/bin/env python3
import os, json, math, hashlib, csv, time, sys
from pathlib import Path

# --- config/inputs ---
root   = Path('.').resolve()
ls3d   = Path(os.environ.get('LS3DW_HOME','LS3D-W')).resolve()
stamp  = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
runout = root/'.tau_ledger'/'ls3dw_runs'/stamp
runout.mkdir(parents=True, exist_ok=True)

# --- deps: try OpenCV, else Pillow ---
try:
    import cv2
    def load_image(path):
        im = cv2.imread(str(path))
        if im is None: return None
        import numpy as np
        return cv2.cvtColor(im, cv2.COLOR_BGR2RGB)
except Exception:
    try:
        from PIL import Image
        import numpy as np
        def load_image(path):
            try: return np.array(Image.open(path).convert('RGB'))
            except Exception: return None
    except Exception as e:
        sys.exit(f"[fatal] Need OpenCV (cv2) or Pillow installed: {e}")

# --- mediapipe ---
try:
    import mediapipe as mp
    mp_fm = mp.solutions.face_mesh
    detector = mp_fm.FaceMesh(static_image_mode=True, refine_landmarks=True, max_num_faces=1)
except Exception as e:
    sys.exit(f"[fatal] Need mediapipe installed: {e}")

def sha256_canon(obj):
    b = json.dumps(obj, sort_keys=True, separators=(",",":")).encode("utf-8")
    return hashlib.sha256(b).hexdigest()

def pca_axes(points):
    import numpy as np
    P = np.asarray(points, float)
    C = P.mean(axis=0)
    Q = P - C
    S = (Q.T @ Q) / max(len(P)-1, 1)
    w,V = np.linalg.eigh(S)  # ascending
    pc1,pc2,pc3 = V[:,2], V[:,1], V[:,0]
    return C, pc1, pc2, pc3

def symmetry_rms(points):
    import numpy as np
    C, n, *_ = pca_axes(points)  # n ≈ left-right normal
    P = np.asarray(points, float)
    n = n / (np.linalg.norm(n) + 1e-12)
    d = (P - C) @ n
    return float(np.sqrt((d*d).mean()))

def angle_deg(a,b,c):
    import numpy as np
    A,B,C = map(lambda v: np.asarray(v,float), (a,b,c))
    u=A-B; v=C-B
    nu=float(np.linalg.norm(u)); nv=float(np.linalg.norm(v))
    if nu<1e-12 or nv<1e-12: return None
    x=float((u@v)/(nu*nv)); x=max(-1.0, min(1.0, x))
    return float(math.degrees(math.acos(x)))

def convexity_heuristic(points):
    import numpy as np
    C, pc1, pc2, pc3 = pca_axes(points)
    P = np.asarray(points, float); Q = P - C
    U = np.stack([pc1,pc2,pc3], axis=1)
    L = Q @ U
    i_brow = int(L[:,1].argmax())
    i_chin = int(L[:,1].argmin())
    i_nose = int(L[:,2].argmax())
    return angle_deg(P[i_brow], P[i_nose], P[i_chin])

def process_image(img_path: Path, rel_id: str):
    import numpy as np
    rgb = load_image(img_path)
    if rgb is None: return None
    h,w = rgb.shape[:2]
    res = detector.process(rgb)
    if not res.multi_face_landmarks: return None
    lm = res.multi_face_landmarks[0].landmark
    pts = [[l.x*w, l.y*h, l.z*max(w,h)] for l in lm]  # scale normalized coords
    trace = {
        "face_id": rel_id,
        "face_landmarks_468x3": pts,
        "face_timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "face_sequence_number": 0
    }
    try: trace["symmetry_rms"]      = symmetry_rms(pts)
    except Exception: pass
    try: trace["convexity_deg_est"] = convexity_heuristic(pts)
    except Exception: pass
    trace["face_signature"] = sha256_canon(trace)
    return trace

exts = {'.jpg','.jpeg','.png','.bmp','.tif','.tiff'}
scanned=kept=0
for p in ls3d.rglob('*'):
    if not p.is_file() or p.suffix.lower() not in exts: continue
    scanned += 1
    rel = p.relative_to(ls3d).as_posix()
    t = process_image(p, rel)
    if not t: continue
    # policy gates (heuristic if confidence absent)
    ok_sym  = (t.get("symmetry_rms") is not None) and (float(t["symmetry_rms"]) <= 0.004)
    ok_conv = (t.get("convexity_deg_est") is not None) and (float(t["convexity_deg_est"]) >= 177.0)
    if not (ok_sym and ok_conv): 
        continue
    kept += 1
    h = t["face_signature"]
    d = runout/h; d.mkdir(parents=True, exist_ok=True)
    (d/'face_trace.json').write_text(json.dumps(t, sort_keys=True, separators=(",",":")), encoding='utf-8')

# build census for this run
rows=[]
for p in runout.rglob('face_trace.json'):
    d=json.loads(p.read_text(encoding='utf-8'))
    rows.append([d.get('face_signature'), d.get('convexity_deg') or d.get('convexity_deg_est'),
                 d.get('symmetry_rms'), d.get('face_confidence'), 'unknown', str(p.relative_to(root))])

outtsv = root/'.tau_ledger'/'census'/'census_full.tsv'
outtsv.parent.mkdir(parents=True, exist_ok=True)
with outtsv.open('w',encoding='utf-8',newline='') as f:
    wr=csv.writer(f, delimiter='\t')
    wr.writerow(['hash','convexity_deg','symmetry_rms','confidence','tier','source_path'])
    for r in rows: wr.writerow(r)

print(f"[sweep] scanned={scanned} admitted={kept} run_dir={runout}")
print(f"[census] wrote {outtsv}")
