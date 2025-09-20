#!/usr/bin/env python3
import sys, os
from pathlib import Path
try:
    import numpy as np
    import torchfile
except Exception as e:
    print("Missing deps (numpy/torchfile):", e, file=sys.stderr); sys.exit(2)

def shp(x):
    try: return tuple(np.asarray(x).shape)
    except: return None

def walk(x, depth=0, path=""):
    if depth>3: return
    s = shp(x)
    if s and any(d in (2,3) for d in s) and max(s)>=60:
        print("  CAND:", path or "<root>", "SHAPE:", s, "TYPE:", type(x).__name__)
    # Recurse shallowly
    if isinstance(x, dict):
        for k,v in list(x.items())[:30]:
            if isinstance(k,str) and k.startswith("__"): continue
            print("  KEY:", k, "SHAPE:", shp(v), "TYPE:", type(v).__name__)
        for k,v in list(x.items())[:30]:
            if isinstance(k,str) and k.startswith("__"): continue
            walk(v, depth+1, f"{path}.{k}" if path else str(k))
    elif isinstance(x, (list,tuple)):
        print("  LISTLEN:", len(x))
        for i,v in enumerate(x[:20]):
            print("  ITEM", i, "SHAPE:", shp(v), "TYPE:", type(v).__name__)
        for i,v in enumerate(x[:20]):
            walk(v, depth+1, f"{path}[{i}]")

def main():
    if len(sys.argv)<2:
        print("usage: peek_t7.py /path/to/file.t7", file=sys.stderr); sys.exit(2)
    p = Path(sys.argv[1])
    print("FILE:", p)
    obj = torchfile.load(str(p))
    print("TOP:", type(obj).__name__, "SHAPE:", shp(obj))
    walk(obj, 0, "")
if __name__ == "__main__":
    main()
