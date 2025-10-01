#!/usr/bin/env python3
import json,glob,time
def latest(p): xs=sorted(glob.glob(p)); return xs[-1] if xs else None
src=latest("analysis/freed/sigma_leaf_*.json")
if not src:
  S=[{"ell":0.0,"sigma_diag":[1.0,1.0,1.0]},
     {"ell":1.0,"sigma_diag":[1.0,1.0,1.0]}]
else:
  S=json.load(open(src,"r",encoding="utf-8"))
S=sorted(S,key=lambda r:r.get("ell",0.0))
def tr_Sinv_dS(a,b):
  da=[(bj-aj) for aj,bj in zip(a,b)]
  s=0.0
  for aj,d in zip(a,da):
    s += d/(aj if abs(aj)>1e-300 else 1e-300)
  return s
tr_vals=[]; hol=0.0
for u,v in zip(S[:-1],S[1:]):
  ell=(u["ell"]+v["ell"])/2.0
  t=tr_Sinv_dS(u["sigma_diag"],v["sigma_diag"])
  tr_vals.append({"ell":ell,"trace":t}); hol+=t
out={"angle":"Determinant/eta curvature",
     "trace_samples":tr_vals,
     "holonomy_smoke":hol,
     "holonomy_is_flat":abs(hol)<=1e-9,
     "_freed_section":"2.6",
     "_freed_citation":"Freed et al. (2024), Sec 2.6"}
stamp=time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())
dst="analysis/freed/det_eta_curvature_"+stamp+".json"
json.dump(out,open(dst,"w",encoding="utf-8"),ensure_ascii=False,indent=2)
print(dst)
