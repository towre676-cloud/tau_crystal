#!/usr/bin/env python3
import json, math, os, sys
def one_loop_mu(b, mu0, ell): 
    pole = 1.0/(b*mu0)
    if ell >= pole: raise ValueError("ell beyond pole")
    return mu0/(1.0 - b*mu0*ell)

def comp_residual(b, mu0, ell1, ell2):
    lhs = one_loop_mu(b, mu0, ell1+ell2)
    mid = one_loop_mu(b, mu0, ell1)
    rhs = one_loop_mu(b, mid,  ell2)
    return abs((lhs - rhs)/lhs)

def rel_line_value(logZ):
    # Relative line element as phase/volume; here just scalar for receipt.
    return math.exp(logZ)

def main():
    b   = float(os.getenv("REL_B","1.0"))
    mu0 = float(os.getenv("REL_MU0","0.1"))
    ell1= float(os.getenv("REL_L1","0.21"))
    ell2= float(os.getenv("REL_L2","0.37"))
    # toy Lagrangian integral along the leaf (replace by your scored integral if desired)
    logZ1 = - b*mu0*ell1
    mu_mid= one_loop_mu(b, mu0, ell1)
    logZ2 = - b*mu_mid*ell2
    logZ12= - b*mu0*(ell1+ell2)
    res_comp = comp_residual(b, mu0, ell1, ell2)
    res_line = abs((rel_line_value(logZ1)*rel_line_value(logZ2) - rel_line_value(logZ12)) / rel_line_value(logZ12))
    out = {
        "kind":"relative_functor",
        "params":{"b":b,"mu0":mu0,"ell1":ell1,"ell2":ell2},
        "mu_comp_residual":res_comp,
        "line_multiplicativity_residual":res_line,
        "tol_mu":1e-12,
        "tol_line":1e-12,
        "pass": (res_comp<1e-12 and res_line<1e-12)
    }
    print(json.dumps(out, indent=2))
if __name__=="__main__": main()
