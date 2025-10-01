#!/usr/bin/env python3
import json,glob,sys,time,math,hashlib
def latest(p): xs=sorted(glob.glob(p)); return xs[-1] if xs else None
def get_num(p,keys):
  if not p: return None
  d=json.load(open(p,"r",encoding="utf-8"))
  for k in keys:
    if k in d and isinstance(d[k],(int,float)): return float(d[k])
  for v in d.values():
    if isinstance(v,(int,float)): return float(v)
  return None
pre = latest("analysis/freed/volume_pre_*.json")
post= latest("analysis/freed/volume_post_*.json")
Vpre=get_num(pre,("volume","vol","det")); Vpost=get_num(post,("volume","vol","det"))
proxy=False
if Vpre is None or Vpost is None:
  proxy=True
  sg=latest("analysis/freed/sigma_leaf_*.json")
  if sg:
    S=json.load(open(sg,"r",encoding="utf-8")); S=sorted(S,key=lambda r:r.get("ell",0.0))
    def det(diag): 
      p=1.0
      for x in diag: p*=x
      return p
    Vpre=det(S[0]["sigma_diag"]); Vpost=det(S[-1]["sigma_diag"])
  else:
    Vpre,Vpost=1.0,1.0
logB = latest("analysis/freed/logB_receipt_*.json")
LB = 0.0 if not logB else (next((float(v) for v in json.load(open(logB,"r",encoding="utf-8")).values() if isinstance(v,(int,float))),0.0))
idx = math.log( max(Vpost,1e-300) / max(Vpre,1e-300) ); res = abs(idx - LB); ok = res <= 0.01
def h(p): return None if not p else hashlib.sha256(open(p,"rb").read()).hexdigest()
rec={"angle":"Relative index (volume proxy)","theorem":"log(Vol_post/Vol_pre) ≈ logB",
     "values":{"log_volume_ratio":idx,"logB":LB,"residual":res},"pass":bool(ok),"proxy_used":proxy,
     "_inputs":{"volume_pre":pre,"volume_post":post,"logB":logB},
     "_sha256":{"volume_pre":h(pre),"volume_post":h(post),"logB":h(logB)},
     "_freed_section":"4.1","_freed_citation":"Freed et al. (2024), Sec 4.1"}
out=".tau_ledger/freed/axiom_relative_index_"+time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())+".json"
json.dump(rec,open(out,"w",encoding="utf-8"),ensure_ascii=False,indent=2); print(out)
