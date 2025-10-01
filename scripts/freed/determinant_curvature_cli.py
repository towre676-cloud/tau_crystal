#!/usr/bin/env python3
import json, math, os
import numpy as np

def mu_of_ell(b, mu0, ell):
    return mu0/(1.0 - b*mu0*ell)

def toy_Sigma(mu):
    # Smooth positive-definite toy Σ(mu); replace with real Σ if available
    M = np.array([[1+0.2*mu, 0.05*mu, 0, 0, 0],
                  [0.05*mu, 1+0.1*mu, 0.02*mu, 0, 0],
                  [0, 0.02*mu, 1+0.15*mu, 0.01*mu, 0],
                  [0, 0, 0.01*mu, 1+0.12*mu, 0.02*mu],
                  [0, 0, 0, 0.02*mu, 1+0.18*mu]])
    return (M+M.T)/2

def main():
    b   = float(os.getenv("DET_B","1.0"))
    mu0 = float(os.getenv("DET_MU0","0.1"))
    L   = float(os.getenv("DET_ELL","0.6"))  # stay below pole
    K   = int(os.getenv("DET_STEPS","64"))
    ells= np.linspace(0, L, K+1)
    logs, traces, muvals = [], [], []
    last_logdet = None
    ok = True
    for i,ell in enumerate(ells):
        mu = mu_of_ell(b, mu0, ell); muvals.append(mu)
        S  = toy_Sigma(mu)
        logdet = np.log(np.linalg.det(S))
        if i>0:
            dlog = (logdet - last_logdet)/(ells[i]-ells[i-1])
            Sinv = np.linalg.inv(S)
            # finite-diff for dSigma/dell
            mu_prev = mu_of_ell(b, mu0, ells[i-1])
            S_prev = toy_Sigma(mu_prev)
            dS = (S - S_prev)/(ells[i]-ells[i-1])
            tr_term = np.trace(Sinv @ dS)
            logs.append(dlog); traces.append(tr_term)
        last_logdet = logdet
    resid = float(np.max(np.abs(np.array(logs)-np.array(traces)))) if logs else 0.0
    out = {
        "kind":"determinant_curvature",
        "params":{"b":b,"mu0":mu0,"L":L,"steps":K},
        "max_residual":resid,
        "tol":1e-6,
        "pass": (resid<1e-6)
    }
    print(json.dumps(out, indent=2))
if __name__=="__main__": main()
