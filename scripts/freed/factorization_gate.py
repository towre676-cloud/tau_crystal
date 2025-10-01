#!/usr/bin/env python3
import json, math, os
def mu(b, mu0, ell): return mu0/(1.0 - b*mu0*ell)
def N_of_ell(b, mu0, ell): return (1.0/(6.0*b))*math.log(1.0/(1.0 - b*mu0*ell))
def ell_k(b, mu0, k): return (1.0/(b*mu0))*(1.0 - math.exp(-3.0*b*k))
def logB_segment(b, mu0, a, c):
    # toy segment contribution: integral of b*mu over [a,c]
    steps=256; h=(c-a)/steps; s=0.0
    for j in range(steps): t=a+(j+0.5)*h; s+= b*mu(b, mu0, t)
    return s*h
def main():
    b=float(os.getenv("FAC_B","1.0")); mu0=float(os.getenv("FAC_MU0","0.1"))
    L=float(os.getenv("FAC_ELL","0.62"))
    total=logB_segment(b, mu0, 0.0, L)
    walls=[ell_k(b, mu0, k) for k in range(1,7) if ell_k(b,mu0,k) <= L] + [L]
    segs=[0.0]+walls
    parts=[logB_segment(b, mu0, segs[i], segs[i+1]) for i in range(len(segs)-1)]
    resid=abs(total - sum(parts))
    out={"kind":"factorization_gate","params":{"b":b,"mu0":mu0,"L":L},
         "total":total,"sum_parts":sum(parts),"residual":resid,"tol":1e-10,"pass":resid<1e-10}
    print(json.dumps(out, indent=2))
if __name__=="__main__": main()
