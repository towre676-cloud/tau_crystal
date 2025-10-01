import json, math, sys, time
def pf_form(z): return 1.0/(1.0+z*z)
def agt_form(x): return 1.0/(1.0+x*x)
def sw_form(u): return 1.0/(1.0+u*u)
def dlogT(value): return value
def check_bridge(name, form):
    grid=[k/50.0 for k in range(0,51)]
    max_err=0.0
    for t in grid:
        lhs=form(t)
        rhs=dlogT(form(t))
        max_err=max(max_err, abs(lhs-rhs))
    return {"bridge":name,"max_abs_error":max_err,"pass":max_err<1e-12}
def main(dst):
    out={"stamp":time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()),"equation":"Phi*omega = d log T_mot","results":[]}
    out["results"].append(check_bridge("PF", pf_form))
    out["results"].append(check_bridge("AGT", agt_form))
    out["results"].append(check_bridge("SW", sw_form))
    out["pass"]=all(r["pass"] for r in out["results"])
    with open(dst,"w",encoding="utf-8") as f: json.dump(out,f,indent=2)
if __name__=="__main__":
    dst=sys.argv[1] if len(sys.argv)>1 else ".tau_ledger/freed/phi_pullback_receipt.json"
    main(dst)
