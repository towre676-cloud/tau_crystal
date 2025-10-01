#!/usr/bin/env python3
import json, math, os
LEVELS = [4,6,8,9,12,18,24,30]  # broadened set
def penalty_level(N):
    # toy modular penalty weight; real impl would tie to congruence level effects
    return 1.0 + 0.01*math.log(1+N)
def logB_base(): return 1.2345  # placeholder baseline
def main():
    phi_on = bool(int(os.getenv("TMF_PHI","0")))
    base = logB_base()
    rows=[]
    for N in LEVELS:
        w=penalty_level(N)*(1.01 if phi_on else 1.0)
        val= base/w
        rows.append({"level":N,"logB_level":val})
    # stability metric: max spread relative to mean
    vals=[r["logB_level"] for r in rows]
    mean=sum(vals)/len(vals); spread=max(vals)-min(vals); rel=spread/max(1e-12,abs(mean))
    out={"kind":"tmf_levels","phi_on":phi_on,"rows":rows,"relative_spread":rel,"tol":0.02,"pass":rel<0.02}
    print(json.dumps(out, indent=2))
if __name__=="__main__": main()
