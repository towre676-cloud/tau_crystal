import sys
p=sys.argv[1]; best=None
with open(p,"r",encoding="utf-8") as fh:
    next(fh)
    for line in fh:
        n,s,t,d,a,b = line.strip().split("\t")
        d=float(d)
        if best is None or d < best[0]: best=(d,n,s,t,a,b)
print("Delta_min=",best[0]," n=",best[1]," s=",best[2]," t=",best[3]," a=",best[4]," b=",best[5])
