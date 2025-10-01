#!/usr/bin/env python3
import json,sys,time,hashlib,os
def h(p): return hashlib.sha256(open(p,"rb").read()).hexdigest()
def num(p):
  d=json.load(open(p,"r",encoding="utf-8"))
  for v in d.values():
    if isinstance(v,(int,float)): return float(v)
  raise SystemExit("no numeric in "+p)
if len(sys.argv)<3: raise SystemExit("usage: atlas_swap.py <A> <B> <tol=1e-12>")
A,B=sys.argv[1],sys.argv[2]; tol=float(sys.argv[3]) if len(sys.argv)>3 else 1e-12
for p in (A,B):
  if not (p and os.path.exists(p) and os.path.getsize(p)>0): raise SystemExit("missing: "+str((A,B)))
la,lb=num(A),num(B); res=abs(la-lb); ok=res<=tol
rec={"angle":"Atlas swap","theorem":"permute coords ⇒ same logB","tolerance":tol,
     "values":{"logB_A":la,"logB_B":lb,"residual":res},"pass":bool(ok),
     "_inputs":{"A":A,"B":B}, "_sha256":{"A":h(A),"B":h(B)},
     "_freed_section":"2.6","_freed_citation":"Freed et al. (2024), Sec 2.6"}
out=".tau_ledger/freed/axiom_atlas_swap_"+time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())+".json"
json.dump(rec,open(out,"w",encoding="utf-8"),ensure_ascii=False,indent=2); print(out)
