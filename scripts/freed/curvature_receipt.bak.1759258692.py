import os, json, time, math, hashlib, sys
try:
    from scripts.freed.nd_kernel import lam_and_dlam
except Exception:
    # stdlib fallback diagonal spectrum
    def lam_and_dlam(mu: float):
        a=[2.0,2.5,3.0,3.5,4.0]; b=[0.30,-0.20,0.15,-0.10,0.05]; c=[0.02,0.03,0.01,0.015,0.025]
        lam=[a[i]+b[i]*mu+c[i]*mu*mu for i in range(5)]
        dlam=[b[i]+2.0*c[i]*mu for i in range(5)]
        for i in range(5):
            if lam[i]<=1e-12: lam[i]=1e-12
        return lam,dlam
def sha256(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for ch in iter(lambda:f.read(1<<20),b''): h.update(ch)
    return h.hexdigest()
def mu_one_loop(mu0,b,ell):
    d=1.0-b*mu0*ell
    if d==0.0: d=1e-16
    return mu0/d
def main():
    os.makedirs("analysis/freed",exist_ok=True)
    os.makedirs(".tau_ledger/freed",exist_ok=True)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    run_id=f"curv_{ts}"
    mu0=float(os.environ.get("FREED_MU0","0.9"))
    b  =float(os.environ.get("FREED_B","0.02"))
    L  =float(os.environ.get("FREED_ELL","12.0"))
    steps=int(os.environ.get("FREED_STEPS","121"))
    xs=[i*L/(steps-1) for i in range(steps)]
    mus=[mu_one_loop(mu0,b,x) for x in xs]
    # derivative dmu/dell = b mu^2
    dmu=[b*m*m for m in mus]
    # compute trace identity vs finite diff
    tr_vals=[]; dlogdet=[]
    for m,dm in zip(mus,dmu):
        lam,dlam=lam_and_dlam(m)
        tr=sum((dlam[i]*dm)/lam[i] for i in range(5))
        tr_vals.append(tr)
    # finite difference of log det Σ(ell)
    import numpy as np  # not available. use stdlib
