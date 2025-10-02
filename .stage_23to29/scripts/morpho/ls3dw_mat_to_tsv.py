#!/usr/bin/env python3
import sys, os
from pathlib import Path
import numpy as np
from scipy.io import loadmat

def find_pts(d):
    # common keys in LS3D-W / 300W-LP variants
    for k in ["pts_3d","landmarks3d","pts3d","S",
              "pts","landmarks","points","pts_2d","landmarks2d"]:
        if k in d:
            a = np.asarray(d[k]).astype(float)
            # squeeze awkward shapes to (N,2/3)
            while a.ndim > 2: a = a.squeeze(axis=tuple(range(a.ndim-2)))
            if a.ndim == 1 and a.size in (136,196): a = a.reshape((-1,2))
            if a.ndim == 2 and a.shape[1] in (2,3): return a
            if a.ndim == 2 and a.shape[0] in (2,3): return a.T
    # try nested dicts
    for v in d.values():
        if isinstance(v, dict):
            r = find_pts(v)
            if r is not None: return r
    return None

def main():
    if len(sys.argv) < 3:
        print("usage: ls3dw_mat_to_tsv.py MAT_DIR OUT_TSV", file=sys.stderr); sys.exit(2)
    src = Path(sys.argv[1]); out = Path(sys.argv[2])
    out.parent.mkdir(parents=True, exist_ok=True)
    w = 0; s = 0
    with open(out, "w", encoding="utf-8") as fo:
        for p in src.rglob("*.mat"):
            s += 1
            try:
                d = loadmat(str(p), squeeze_me=True, struct_as_record=False)
                pts = find_pts(d)
                if pts is None: continue
                if pts.shape[1] == 2:  # add z=0
                    pts = np.concatenate([pts, np.zeros((pts.shape[0],1))], axis=1)
                rid = p.stem
                row = [rid] + [f"{v:.8f}" for xyz in pts for v in xyz]
                fo.write("\t".join(row) + "\n")
                w += 1
            except Exception:
                pass
            if s % 500 == 0:
                print(f"[progress] scanned={s} written={w}")
    print(f"WROTE_ROWS={w}")
    sys.exit(0 if w>0 else 1)

if __name__ == "__main__":
    main()
