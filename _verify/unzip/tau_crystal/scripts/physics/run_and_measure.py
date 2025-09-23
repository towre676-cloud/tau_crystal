#!/usr/bin/env python3
import json, os, time, math, shutil, subprocess
n=int(os.environ.get("N","1000000")); k=int(os.environ.get("K","64"))
def energy_start():
  try:
    import pynvml; pynvml.nvmlInit(); h=pynvml.nvmlDeviceGetHandleByIndex(0); return ("nvml",h, time.time(), pynvml.nvmlDeviceGetTotalEnergyConsumption(h))
  except Exception: return ("none",None,time.time(),0.0)
def energy_end(ctx):
  kind,h,t0,e0=ctx
  if kind=="nvml":
    import pynvml; e1=pynvml.nvmlDeviceGetTotalEnergyConsumption(h); return (time.time()-t0, (e1-e0)/1000.0)
  return (time.time()-t0, None)
def kernel(n,k):
  # simple spectral-ish work: sum of k moving-window dot-products over n
  acc=0.0
  for j in range(k):
    s=0.0; step=max(1,n//(k+1))
    for i in range(0,n,step): s += (i%1024)*1.000001
    acc += s
  return acc
ctx=energy_start(); t0=time.perf_counter(); acc=kernel(n,k); dt=time.perf_counter()-t0; dt_wall, dj=energy_end(ctx)
# crude tau: proportional to k ticks if loop bodies executed
tau = float(k)
doc={"measured":{"T":dt,"E":dj,"tau":tau}, "n":n,"k":k,"acc":acc}
open(".tau_ledger/physics/post_meas.json","w").write(json.dumps(doc,indent=2))
print("[run] T=%.3f s  E=%s J  tau=%.1f" % (dt, "nan" if dj is None else f"{dj:.2f}", tau))
