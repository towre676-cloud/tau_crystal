import sys, os
p=sys.argv[1]
best=None
with open(p,"r",encoding="utf-8") as fh:
    next(fh)
    for line in fh:
        n,s,t,d,a,b = line.rstrip("\\n").split("\\t")
        d=float(d)
        if best is None or d < best[0]: best=(d,n,s,t,a,b)
d,n,s,t,a,b = best
print(f"best: Delta={d} n={n} s={s} t={t} a={a} b={b}")
go=os.environ.get("GITHUB_OUTPUT")
if go:
    with open(go,"a",encoding="utf-8") as fh:
        fh.write(f"BEST_DELTA={d}\\n")
        fh.write(f"BEST_N={n}\\n")
        fh.write(f"BEST_S={s}\\n")
        fh.write(f"BEST_T={t}\\n")
