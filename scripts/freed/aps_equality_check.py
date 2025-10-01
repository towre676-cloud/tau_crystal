#!/usr/bin/env python3
import json,sys,os,hashlib,time
def sha(p): h=hashlib.sha256(); h.update(open(p,"rb").read()); return h.hexdigest()
def num(d,keys):
  for k in keys:
    if k in d and isinstance(d[k],(int,float)): return float(d[k])
  for v in d.values():
    if isinstance(v,(int,float)): return float(v)
  raise SystemExit("numeric not found")
bulk,eta,logB=sys.argv[1:4]
tol=float(os.environ.get("APS_TOL","1e-9"))
Db=json.load(open(bulk,"r",encoding="utf-8"))
De=json.load(open(eta,"r",encoding="utf-8"))
Dl=json.load(open(logB,"r",encoding="utf-8"))
bv=num(Db,("bulk","bulk_logdet","logdet","value"))
ev=num(De,("eta","eta_over_2","value"))
lv=num(Dl,("logB","log_ratio","log_evidence","value"))
lhs=lv; rhs=bv-0.5*ev
diff=lhs-rhs; n=int(round(diff)); resid=abs(diff-n); ok=resid<=tol
rec={"angle":"APS split equality","theorem":"logB = bulk - eta/2 + Z","tolerance":tol,
     "values":{"logB":lhs,"bulk":bv,"eta":ev,"rhs":rhs,"diff":diff,"nearest_Z":n,"residual":resid},
     "pass":bool(ok),
     "_inputs":{"bulk":bulk,"eta":eta,"logB":logB},
     "_sha256":{"bulk":sha(bulk),"eta":sha(eta),"logB":sha(logB)},
     "_freed_section":"4.1","_freed_citation":"Freed et al. (2024), Sec 4.1"}
out=".tau_ledger/freed/axiom_aps_split_"+time.strftime("%Y%m%dT%H%M%SZ",time.gmtime())+".json"
json.dump(rec,open(out,"w",encoding="utf-8"),ensure_ascii=False,indent=2); print(out)
