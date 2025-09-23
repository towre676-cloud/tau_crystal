#!/usr/bin/env python3
import sys, os, hashlib
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
    if h in (2,3) and w not in (2,3):  # transpose if coords are rows
        a = a.T; h,w = a.shape
    if w == 2:
        z = np.zeros((h,1), dtype=float); a = np.concatenate([a,z], axis=1)
    elif w != 3:
        raise RuntimeError(f"bad width {w}")
    return a  # (N,3)

def extract_any_landmarks(obj):
    import numpy as np
    prefer = {"pts_3d","landmarks3d","pts3d","points3d","lm3d",
              "pts","landmarks","points","lm","shape","S"}
    cand = []
    def walk(x, depth=0):
        if depth>4:  # avoid pathological recursion
            return
        # try as array
        try:
            a = to_np(x)
            if a.ndim in (2,3):
                shp = a.shape
                if any(d in (2,3) for d in shp) and max(shp) >= 60:
                    cand.append(a)
        except Exception:
            pass
        # recurse
        if isinstance(x, dict):
            for k,v in x.items():
                if isinstance(k,str) and k.startswith("__"): continue
                walk(v, depth+1)
        elif isinstance(x, (list,tuple)):
            for v in x[:32]:
                walk(v, depth+1)
    walk(obj)
    # prefer named keys if present
    if isinstance(obj, dict):
        for k in list(obj.keys()):
            if k in prefer:
                try:
                    return as_nx3(obj[k])
                except Exception:
                    pass
    # fallback first workable
    for a in cand:
        try:
            return as_nx3(a)
        except Exception:
            pass
    raise RuntimeError("no landmark-like array")

def load_t7(p):
    import torchfile
    return torchfile.load(p)

def stable_shard(s: str, shards: int) -> int:
    h = hashlib.sha1(s.encode('utf-8')).digest()
    return int.from_bytes(h[:4], 'big') % shards

def main():
    if len(sys.argv) < 5:
        print("usage: ls3dw_t7_to_tsv_sharded.py SRC_DIR OUT_DIR --shards N --shard-index K [--limit M] [--progress]", file=sys.stderr)
        sys.exit(2)
    src = Path(sys.argv[1]); outdir = Path(sys.argv[2])
    shards = int(sys.argv[4]); shard_idx = int(sys.argv[6]) if sys.argv[5] == "--shard-index" else None
    if shard_idx is None:
        print("missing --shard-index K", file=sys.stderr); sys.exit(2)
    limit = None; progress = False
    if "--limit" in sys.argv:
        i = sys.argv.index("--limit"); limit = int(sys.argv[i+1])
    if "--progress" in sys.argv:
        progress = True

    outdir.mkdir(parents=True, exist_ok=True)
    out_path = outdir / f"ls3d_landmarks.{shard_idx}.tsv"

    # Resume support: build a small set of already-written IDs
    seen_ids = set()
    if out_path.exists():
        try:
            with open(out_path, "r", encoding="utf-8", errors="ignore") as fi:
                for line in fi:
                    if not line: continue
                    rid = line.split("\t",1)[0].strip()
                    if rid: seen_ids.add(rid)
        except Exception:
            pass

    scanned=0; written=0
    with open(out_path, "a", encoding="utf-8") as fo:
        for p in src.rglob("*.t7"):
            rid = p.stem
            if stable_shard(str(p), shards) != shard_idx:
                continue
            scanned += 1
            if limit is not None and scanned > limit:
                break
            if rid in seen_ids:
                continue
            try:
                obj = load_t7(str(p))
                pts = extract_any_landmarks(obj)
                row = [rid] + [f"{v:.8f}" for xyz in pts for v in xyz]
                fo.write("\t".join(row) + "\n")
                written += 1
            except Exception:
                pass
            if progress and scanned % 1000 == 0:
                print(f"[shard {shard_idx}] scanned={scanned} appended={written}")
    print(f"SHARD={shard_idx} SCANNED={scanned} WROTE_ROWS={written} OUT={out_path}")
    if written==0 and len(seen_ids)==0:
        # no new rows and not previously written: hint
        print("no .t7 landmarks converted in this shard — may be empty or keys differ", file=sys.stderr)

if __name__ == "__main__":
    # argv form: SRC OUTDIR --shards N --shard-index K [--limit M] [--progress]
    main()
