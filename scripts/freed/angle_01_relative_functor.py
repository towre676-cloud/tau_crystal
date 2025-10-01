#!/usr/bin/env python3
import json,sys,time,hashlib,os
def h(p): return hashlib.sha256(open(p,"rb").read()).hexdigest()
def num(p):
  d=json.load(open(p,"r",encoding="utf-8"))
  for v in d.values():
    if isinstance(v,(int,float)): return float(v)
  raise SystemExit("no numeric in "+p)
if len(sys.argv)<4: raise SystemExit("usage: relative_functor.py <segA> <segB> <whole> [tol]")
A,B,W=sys.argv[1],sys.argv[2],sys.argv[3]
tol=float(sys.argv[4]) if len(sys.argv)>4 else 1e-9
for p in (A,B,W):
  if not (p and os.path.exists(p) and os.path.getsize(p)>0): raise SystemExit("missing: "+str((A,B,W)))
la,lb,lw=num(A),num(B),num(W); res=abs((la+lb)-lw); ok=res<=tol
rec={"angle":"Relative Functor","theorem":"logB(l1)+logB(l2)=logB(l1+l2)","tolerance":tol,
     "values":{"logB_a":la,"logB_b":lb,"logB_whole":lw,"residual":res},"pass":bool(ok),
     "_inputs":{"a":A,"b":B,"whole":W},"_sha256":{"a":h(A),"b":h(B),"whole":h(W)},
     "_freed_section":"2.1","_freed_citation":"Freed et al. (2024), Sec 2.1"}
out=".tau_ledger/freed/axiom_relative_functor_"+time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())+".json"
json.dump(rec,open(out,"w",encoding="utf-8"),ensure_ascii=False,indent=2); print(out)
