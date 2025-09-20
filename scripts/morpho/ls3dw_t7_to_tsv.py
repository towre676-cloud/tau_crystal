#!/usr/bin/env python3
import sys, os
from pathlib import Path

def to_np(x):
    import numpy as np
    return np.asarray(x, dtype=float)

def as_nx3(arr):
    import numpy as np
    a = to_np(arr)
    while a.ndim > 2:
        a = a[0]
    if a.ndim != 2:
        raise RuntimeError(f"ndim={a.ndim}")
    h,w = a.shape
    if h in (2,3) and w not in (2,3):
        a = a.T; h,w = a.shape
    if w == 2:
        z = np.zeros((h,1), dtype=float); a = np.concatenate([a,z], axis=1)
    elif w != 3:
        raise RuntimeError(f"bad width {w}")
    return a

def extract_any_landmarks(obj):
    # Recursively search dicts/lists for an array of shape ~ (N,2) or (N,3) (N>=60)
    import numpy as np
    prefer = {"pts_3d","landmarks3d","pts3d","points3d","lm3d","pts","landmarks","points","lm","shape","S"}
    cand = []
    def walk(x, keypath=""): 
        from collections.abc import Mapping
        try:
            a = to_np(x)
            if a.ndim in (2,3):
                shp = a.shape
                if any(d in (2,3) for d in shp) and max(shp) >= 60:
                    cand.append((keypath, a))
        except Exception:
            pass
        # Recurse
        if isinstance(x, dict):
            for k,v in x.items():
                if k.startswith("__"): continue
                walk(v, f"{keypath}.{k}" if keypath else str(k))
        elif isinstance(x, (list,tuple)):
            for i,v in enumerate(x[:50]):
                walk(v, f"{keypath}[{i}]")
    walk(obj)
    # prefer named keys first
    for kp,a in cand:
        base = kp.split(".")[-1].lower() if kp else ""
        if base in prefer:
            try: return as_nx3(a)
            except Exception: pass
    # else first workable
    for kp,a in cand:
        try: return as_nx3(a)
        except Exception: pass
    raise RuntimeError("no landmark-like array")

def main():
    if len(sys.argv) < 3:
        print("usage: ls3dw_t7_to_tsv.py /path/to/LS3D-W out.tsv [--limit N] [--progress]", file=sys.stderr); sys.exit(2)
    src = Path(sys.argv[1]); out = Path(sys.argv[2])
    limit = None; progress=False
    if "--limit" in sys.argv:
        i = sys.argv.index("--limit"); limit = int(sys.argv[i+1])
    if "--progress" in sys.argv: progress=True
    import torchfile, numpy as np
    out.parent.mkdir(parents=True, exist_ok=True)
    written = 0; seen = 0
    with open(out, "w", encoding="utf-8") as fo:
        for p in src.rglob("*.t7"):
            if limit is not None and seen >= limit: break
            seen += 1
            try:
                obj = torchfile.load(str(p))
                pts = extract_any_landmarks(obj)
                rid = p.stem
                row = [rid] + [f"{v:.8f}" for xyz in pts for v in xyz]
                fo.write("\\t".join(row) + "\\n")
                written += 1
            except Exception:
                pass
            if progress and seen % 1000 == 0:
                print(f"[progress] scanned={seen} written={written}")
    print(f"WROTE_ROWS={written}")
    if written == 0:
        print("no .t7 landmarks converted — check file contents/keys", file=sys.stderr); sys.exit(1)

if __name__ == "__main__": main()
