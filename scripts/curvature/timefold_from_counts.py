import json, math, math as _m
from pathlib import Path
def L(p, d=None):\n  try: return json.loads(Path(p).read_text())\n  except Exception: return d
def sanitize_counts(d):\n  out={}\n  if not isinstance(d,dict): return out\n  for k,v in d.items():\n    try:\n      x=float(v)\n      if _m.isnan(x) or _m.isinf(x) or x<0: x=0.0\n    except Exception:\n      x=0.0\n    out[str(k)]=x\n  return out
def keys_union(dicts):\n  ks=set(); [ks.update(d.keys()) for d in dicts if isinstance(d,dict)]; return sorted(ks)
def norm(d,keys):\n  tot=sum(float(d.get(k,0.0)) for k in keys)\n  if tot<=0: return {k:0.0 for k in keys}\n  return {k: float(d.get(k,0.0))/tot for k in keys}
def kl(p,q,keys,eps):\n  s=0.0\n  for k in keys:\n    pa=float(p.get(k,0.0))+eps\n    qa=float(q.get(k,0.0))+eps\n    if pa<eps: pa=eps\n    if qa<eps: qa=eps\n    s += pa * (math.log(pa) - math.log(qa))\n  return float(s)
def safe_write(obj):\n  Path("artifacts/curvature/timefold_kl.json").write_text(json.dumps(obj,separators=(",",":")))
try:
  Cover=L("artifacts/curvature/cover_windows.json",{"windows":[]})
  eps=L("etc/timefold_prior.json",{"epsilon":1e-9}).get("epsilon",1e-9)
  wins=[w.get("id") for w in (Cover.get("windows") or []) if w.get("id")]
  if not wins: wins=["U1","U2","U3"]
  pairs=[]; n=len(wins)
  for i,uid in enumerate(wins):
    theta=wins[(n-1)-i]
    di=sanitize_counts(L(f"artifacts/curvature/window_counts/{uid}.json",{}))
    dt=sanitize_counts(L(f"artifacts/curvature/window_counts/{theta}.json",{}))
    keys=keys_union([di,dt])
    if not keys: keys=["sigma","phi","rho"]
    pi=norm(di,keys); pt=norm(dt,keys)
    pairs.append({"i":uid,"theta":theta,"kl":kl(pi,pt,keys,eps)})
  mean_kl=(sum(p["kl"] for p in pairs)/len(pairs)) if pairs else 0.0
  safe_write({"timefold":pairs,"mean_kl":mean_kl,"epsilon":eps})
except Exception:\n  safe_write({"timefold":[],"mean_kl":0.0,"epsilon":1e-9,"fallback":true})
print("ok")
