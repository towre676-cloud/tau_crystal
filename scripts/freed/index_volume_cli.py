#!/usr/bin/env python3
import json, math, os, random
random.seed(7)
def penalty_len0(r): return sum(1 for x in r if abs(x)>1e-12)
def denom_complexity(r):
    # pretend rationals p/q; model complexity by sum of small denominators via continued-fraction-ish proxy
    comp=0
    for x in r:
        q=min(30,max(1,int(round(1.0/max(1e-9,abs(x - round(x))))))) if abs(x)>1e-9 else 1
        comp+=q
    return comp
def main():
    n=int(os.getenv("VOL_SAMPLES","4000"))
    lam0=float(os.getenv("VOL_L0","0.4"))
    lamd=float(os.getenv("VOL_LDEN","0.02"))
    lamphi=float(os.getenv("VOL_LPHI","0.3"))
    phi_gate=bool(int(os.getenv("VOL_PHI","0")))
    acc=0.0
    for _ in range(n):
        r=[random.choice([0.0,0.5,-0.5,1/3,-1/3,1/6,-1/6]) for _ in range(5)]
        L = lam0*penalty_len0(r)+lamd*denom_complexity(r)+ (lamphi if phi_gate and abs(r[3])>1e-12 else 0.0)
        acc += math.exp(-L)
    logZ = math.log(acc+1e-300)
    out={"kind":"index_volume","samples":n,"logZ_estimate":logZ,"params":{"lam0":lam0,"lam_den":lamd,"lam_phi":lamphi,"phi_gate":phi_gate}}
    print(json.dumps(out, indent=2))
if __name__=="__main__": main()
