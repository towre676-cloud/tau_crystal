#!/usr/bin/env python3
import os, json, time, math, statistics
from datetime import datetime

# Window & kernel settings (override via env)
N_MIN = int(os.environ.get("N_MIN", "200_000").replace("_",""))
N_MAX = int(os.environ.get("N_MAX", "2_000_000").replace("_",""))
N_SAMPLES = max(3, int(os.environ.get("N_SAMPLES", "5")))
K = int(os.environ.get("K", "96"))
REPEATS = max(1, int(os.environ.get("REPEATS", "1")))

def kernel(n,k):
    # same cheap spectral-ish work as run_and_measure.py
    acc=0.0
    step=max(1,n//(k+1))
    for j in range(k):
        s=0.0
        for i in range(0,n,step):
            s += (i%1024)*1.000001
        acc += s
    return acc

def measure(n,k):
    t0=time.perf_counter()
    kernel(n,k)
    return time.perf_counter()-t0

# Generate window (linear spacing; small, reproducible)
if N_SAMPLES==1:
    grid=[N_MIN]
else:
    step=(N_MAX-N_MIN)/(N_SAMPLES-1)
    grid=[int(N_MIN + i*step) for i in range(N_SAMPLES)]

# Collect (n, T)
pairs=[]
for n in grid:
    ts=[measure(n,K) for _ in range(REPEATS)]
    T=min(ts)
    pairs.append((n,T))

# Fit T ~ a n + b (least squares)
Sx=sum(n for n,_ in pairs); Sy=sum(T for _,T in pairs)
Sxx=sum(n*n for n,_ in pairs); Sxy=sum(n*T for n,T in pairs)
N=len(pairs)
den = (N*Sxx - Sx*Sx) or 1.0
a = (N*Sxy - Sx*Sy)/den
b = (Sy - a*Sx)/N

# Residuals and tolerance metric
res=[abs(T - (a*n + b))/max(T,1e-12) for n,T in pairs]
eta=max(res)

# Stamp into passport
path=".tau_ledger/physics/passport.json"
try:
    doc=json.load(open(path,"r",encoding="utf-8"))
except FileNotFoundError:
    doc={}
doc.setdefault("linear_model",{})
doc["linear_model"].update({
    "k": K,
    "window": {"n_min": grid[0], "n_max": grid[-1], "samples": N_SAMPLES},
    "a": a, "b": b, "eta": eta,
    "captured_at": datetime.now().astimezone().isoformat()
})
os.makedirs(os.path.dirname(path), exist_ok=True)
open(path,"w",encoding="utf-8").write(json.dumps(doc, indent=2))

# Step summary friendly print
print("[calibrate] window nin[%d,%d] k=%d  ->  a=%.3e s/item  b=%.3e s  max residual eta=%.3f"
      % (grid[0], grid[-1], K, a, b, eta))
for n,T in pairs:
    pred=a*n+b
    print("  n=%d  T=%.6f  T^=%.6f  rel=%.3f" % (n, T, pred, abs(T-pred)/max(T,1e-12)))
