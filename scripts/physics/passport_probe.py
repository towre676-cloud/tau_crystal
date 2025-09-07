#!/usr/bin/env python3
import json, os, platform, shutil, subprocess, time, math
from datetime import datetime
def sh(cmd):
  try:
    out = subprocess.check_output(cmd, shell=True, stderr=subprocess.DEVNULL, text=True, timeout=3)
    return out.strip()
  except Exception:
    return ""
def try_int(x, d=None):
  try: return int(x)
  except: return d
def bytes_of(s):
  s=s.lower().strip(); m=1
  for u,k in [("gib",1<<30),("gb",10**9),("mib",1<<20),("mb",10**6)]:
    if s.endswith(u): m=k; s=s[:-len(u)].strip(); break
  try: return int(float(s)*m)
  except: return None
# CPU mem (fallback via psutil if present)
mem_bytes=None
try:
  import psutil
  mem_bytes=psutil.virtual_memory().total
except Exception:
  pass
# GPU profile (optional)
gpu_name, gpu_mem=None, None
if shutil.which("nvidia-smi"):
  q=sh("nvidia-smi --query-gpu=name,memory.total --format=csv,noheader,nounits | head -n 1")
  if q:
    parts=[p.strip() for p in q.split(",")]
    if len(parts)>=2:
      gpu_name=parts[0]; gpu_mem=try_int(parts[1])*10**6 if parts[1] else None
# crude bandwidth probe (copy 512MB if possible)
beta=None
try:
  import mmap, tempfile
  size=min(512*(1<<20), (mem_bytes or (2<<30))//8)
  t0=time.perf_counter();
  a=bytearray(b"\\0")*size; b=bytearray(a);
  dt=time.perf_counter()-t0
  if dt>0: beta=(2*size)/dt
except Exception:
  pass
# record
doc={
  "captured_at": datetime.utcnow().isoformat()+"Z",
  "host": {"system": platform.system(), "release": platform.release(), "machine": platform.machine()},
  "cpu": {"mem_total_bytes": mem_bytes},
  "gpu": {"name": gpu_name, "mem_total_bytes": gpu_mem},
  "io": {"beta_sustained_bytes_per_s": beta},
  "coefficients": {"c_time": None, "c_energy": None, "c_mem": 1.0, "E0": 0.0}
}
out=os.path.join(".tau_ledger","physics","passport.json")
os.makedirs(os.path.dirname(out), exist_ok=True)
open(out,"w",encoding="utf-8").write(json.dumps(doc, indent=2))
print("[passport] wrote", out)
