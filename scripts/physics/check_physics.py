#!/usr/bin/env python3
import json, os, math, sys
pre=json.load(open(".tau_ledger/physics/pre_cert.json"))
post=json.load(open(".tau_ledger/physics/post_meas.json"))
T_hat=pre["predicted"]["T"]; E_hat=pre["predicted"]["E"]; M_hat=pre["predicted"]["M"]
T=post["measured"]["T"]; E=post["measured"]["E"]; tau=post["measured"]["tau"]
L_max=pre["budgets"]["L_max"]; E_max=pre["budgets"]["E_max"]; M_max=pre["budgets"]["M_max"]; TAU=pre["budgets"]["TAU_STAR"]
def rel(a,b):
  return None if (a is None or b in (None,0)) else abs(a-b)/max(abs(b),1e-12)
rT=rel(T,T_hat); rE=None if (E is None or E_hat in (None,0)) else rel(E,E_hat)
T_TOL=float(os.environ.get("T_TOL","0.4"))
ok = (T<=L_max) and (E is None or E<=E_max) and (tau>=TAU*0.95) and ((rT is None) or (rT<=T_TOL))
doc={"pre":pre,"post":post,"residues":{"dT_rel":rT,"dE_rel":rE}, "ok":ok}
open(".tau_ledger/physics/post_cert.json","w").write(json.dumps(doc,indent=2))
print("[check] ok=%s  dT=%.3f  dE=%s" % (ok, -1.0 if rT is None else rT, "nan" if rE is None else f"{rE:.3f}"))
sys.exit(0 if ok else 1)
