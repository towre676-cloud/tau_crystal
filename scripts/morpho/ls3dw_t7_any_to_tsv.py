#!/usr/bin/env python3
import sys
from pathlib import Path

def np_as(x):
    import numpy as np
    return np.asarray(x)

def points_from_array(a):
    import numpy as np
    a = np_as(a).astype(float)
    # squeeze leading dims
    while a.ndim > 2:
        a = a[0]
    if a.ndim == 1:
        n = a.shape[0]
        if n in (136,196):           # 68x2 or 98x2
            a = a.reshape((-1,2))
        else:
            raise RuntimeError(f"1D vector len={n} not 136/196")
    if a.ndim != 2:
        raise RuntimeError(f"points ndim={a.ndim}")
    h,w = a.shape
    if h in (2,3) and w not in (2,3):  # transpose if coords are rows
        a = a.T; h,w = a.shape
    if w == 2:
        z = np.zeros((h,1)); a = np.concatenate([a,z], axis=1)
    elif w != 3:
        raise RuntimeError(f"points width={w} not 2/3")
    return a  # (N,3)

def soft_argmax_2d(hm, eps=1e-8):
    import numpy as np
    H,W = hm.shape
    e = np.exp(hm - hm.max())
    Z = e.sum() + eps
    py = e.sum(axis=1)/Z; px = e.sum(axis=0)/Z
    ys = np.arange(H, dtype=float); xs = np.arange(W, dtype=float)
    y = (py*ys).sum(); x = (px*xs).sum()
    return y, x

def points_from_heatmaps(hms):
    import numpy as np
    a = np_as(hms).astype(float)
    # squeeze but keep 3 dims
    while a.ndim > 3:
        a = a[0]
    if a.ndim != 3:
        raise RuntimeError(f"heatmaps ndim={a.ndim}")
    s = a.shape
    if s[0] in (68,98) and s[1]>3 and s[2]>3:
        K,H,W = s; hms = a
    elif s[2] in (68,98) and s[0]>3 and s[1]>3:
        H,W,K = s; hms = a.transpose(2,0,1)
    else:
        raise RuntimeError(f"heatmaps bad shape={s}")
    K,H,W = hms.shape
    out = np.zeros((K,3), float)
    for k in range(K):
        y,x = soft_argmax_2d(hms[k])
        out[k] = (x,y,0.0)
    return out

def torch_load(p):
    import torchfile
    return torchfile.load(p)

def collect_candidates(x, depth=0, max_depth=4, out=None):
    import numpy as np
    if out is None: out=[]
    if depth>max_depth: return out
    # try array-like
    try:
        a = np_as(x)
        if hasattr(a, "shape"):
            sh = tuple(int(t) for t in a.shape)
            if len(sh)==1 and sh[0] in (136,196):
                out.append(("points", a))
            elif len(sh)==2:
                h,w = sh
                if (h in (2,3) and w>=60) or (w in (2,3) and h>=60) or (h>=60 and w in (2,3)) or (h>=60 and w>=2):
                    out.append(("points", a))
            elif len(sh)==3:
                if (sh[0] in (68,98) and sh[1]>3 and sh[2]>3) or (sh[2] in (68,98) and sh[0]>3 and sh[1]>3):
                    out.append(("heatmaps", a))
    except Exception:
        pass
    # recurse shallowly
    if isinstance(x, dict):
        for k,v in list(x.items())[:40]:
            if isinstance(k,str) and k.startswith("__"): continue
            collect_candidates(v, depth+1, max_depth, out)
    elif isinstance(x, (list,tuple)):
        for v in x[:64]:
            collect_candidates(v, depth+1, max_depth, out)
    return out

def process_one(path):
    obj = torch_load(str(path))
    cands = collect_candidates(obj)
    # 1) try points
    for kind,a in cands:
        if kind!="points": continue
        try:
            return points_from_array(a)
        except Exception:
            pass
    # 2) try heatmaps
    for kind,a in cands:
        if kind!="heatmaps": continue
        try:
            return points_from_heatmaps(a)
        except Exception:
            pass
    raise RuntimeError("no usable array")

def main():
    if len(sys.argv)<3:
        print("usage: ls3dw_t7_any_to_tsv.py SRC_DIR OUT_TSV [--limit N] [--progress]", file=sys.stderr); sys.exit(2)
    src = Path(sys.argv[1]); out = Path(sys.argv[2])
    limit=None; progress=False
    if "--limit" in sys.argv:
        i=sys.argv.index("--limit"); limit=int(sys.argv[i+1])
    if "--progress" in sys.argv: progress=True

    out.parent.mkdir(parents=True, exist_ok=True)
    written=0; scanned=0
    with open(out, "w", encoding="utf-8") as fo:
        for p in src.rglob("*.t7"):
            scanned += 1
            if limit is not None and scanned>limit: break
            try:
                pts = process_one(p)
                rid = p.stem
                row = [rid] + [f"{v:.8f}" for xyz in pts for v in xyz]
                fo.write("\t".join(row) + "\n")
                written += 1
            except Exception:
                pass
            if progress and scanned % 1000 == 0:
                print(f"[progress] scanned={scanned} written={written}")
    print(f"WROTE_ROWS={written}")
    if written==0: sys.exit(1)

if __name__ == "__main__":
    main()
