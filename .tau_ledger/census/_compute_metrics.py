#!/usr/bin/env python3
import csv, json, math, sys
from pathlib import Path

root = Path('.').resolve()
census_in  = root/'.tau_ledger'/'census'/'census.tsv'
census_out = root/'.tau_ledger'/'census'/'census_full.tsv'
cfg_path   = root/'.tau_ledger'/'census'/'face_metrics_config.json'

def load_cfg():
    try:
        return json.loads(cfg_path.read_text(encoding='utf-8'))
    except Exception:
        return {}

def pca_axes(points):
    # points: list of [x,y,z]
    import numpy as np
    P = np.array(points, dtype=float)
    C = P.mean(axis=0)
    Q = P - C
    # covariance
    S = (Q.T @ Q) / max(len(P)-1, 1)
    vals, vecs = np.linalg.eigh(S)  # ascending eigenvalues
    # largest variance axis is the last eigenvector
    pc1 = vecs[:, 2]  # left-right approx
    pc2 = vecs[:, 1]  # up-down approx
    pc3 = vecs[:, 0]  # depth approx
    return C, pc1, pc2, pc3

def symmetry_rms(points):
    # RMS distance of all points to mid-sagittal plane (through mean, normal=pc1)
    import numpy as np
    C, pc1, _, _ = pca_axes(points)
    P = np.array(points, dtype=float)
    # signed distance to plane n·(x-C)=0
    n = pc1 / (np.linalg.norm(pc1) + 1e-12)
    d = (P - C) @ n
    return float(math.sqrt((d*d).mean()))

def angle_deg(a, b, c):
    # angle ABC (at B) in degrees
    import numpy as np
    A,B,C = map(lambda v: np.array(v, dtype=float), (a,b,c))
    u = A - B
    v = C - B
    nu = np.linalg.norm(u); nv = np.linalg.norm(v)
    if nu < 1e-12 or nv < 1e-12: return None
    cosang = float((u @ v) / (nu*nv))
    cosang = max(-1.0, min(1.0, cosang))
    return math.degrees(math.acos(cosang))

def convexity_from_cfg(points, cfg):
    try:
        g = points[int(cfg['glabella'])]
        s = points[int(cfg['subnasale'])]
        p = points[int(cfg['pogonion'])]
        ang = angle_deg(g, s, p)
        return float(ang), "config"
    except Exception:
        return None, "none"

def convexity_heuristic(points):
    # Heuristic: project to PCA frame; pick:
    #  brow = max along PC2, chin = min along PC2, nose tip = max along PC3 (depth/out-of-face)
    import numpy as np
    C, pc1, pc2, pc3 = pca_axes(points)
    P = np.array(points, dtype=float)
    # local coords
    U = np.stack([pc1, pc2, pc3], axis=1)  # columns
    L = (P - C) @ U  # Nx3
    i_brow = int(L[:,1].argmax())
    i_chin = int(L[:,1].argmin())
    i_nose = int(L[:,2].argmax())
    g = P[i_brow].tolist()
    s = P[i_nose].tolist()
    p = P[i_chin].tolist()
    ang = angle_deg(g, s, p)
    return (None if ang is None else float(ang)), "heuristic"

def load_points(json_path: Path):
    try:
        data = json.loads(json_path.read_text(encoding='utf-8'))
        pts = data.get('face_landmarks_468x3')
        if not pts or len(pts) < 10: return None
        return [list(map(float, pt[:3])) for pt in pts]
    except Exception:
        return None

def main():
    cfg = load_cfg()
    rows=[]
    with open(census_in, 'r', encoding='utf-8') as f:
        rd = csv.reader(f, delimiter='\t')
        hdr = next(rd, None)
        for h in rd:
            rows.append({'hash':h[0], 'confidence':h[1] or None, 'tier':h[2], 'source_path':h[3]})
    for r in rows:
        j = (root / r['source_path']).resolve()
        points = load_points(j)
        conv = None; conv_src = 'none'
        sym = None
        if points:
            # symmetry
            try: sym = symmetry_rms(points)
            except Exception: sym = None
            # convexity (cfg preferred)
            conv, conv_src = convexity_from_cfg(points, cfg)
            if conv is None:
                try:
                    conv, conv_src = convexity_heuristic(points)
                except Exception:
                    conv, conv_src = None, 'none'
        r['convexity_deg'] = conv
        r['symmetry_rms']  = sym
        r['convexity_source'] = conv_src
    with open(census_out, 'w', encoding='utf-8', newline='') as f:
        wr = csv.writer(f, delimiter='\t')
        wr.writerow(['hash','convexity_deg','symmetry_rms','confidence','tier','source_path','convexity_source'])
        for r in rows:
            wr.writerow([r['hash'], r['convexity_deg'], r['symmetry_rms'], r['confidence'], r['tier'], r['source_path'], r['convexity_source']])
    print('[compute] wrote', census_out)

if __name__ == '__main__':
    main()
