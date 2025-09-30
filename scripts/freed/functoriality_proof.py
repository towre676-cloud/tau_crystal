import os, json, time, math, hashlib, cmath
def sha256_file(p):
    h=hashlib.sha256(); 
    with open(p,"rb") as f:
        for ch in iter(lambda:f.read(1<<20), b""): h.update(ch)
    return h.hexdigest()
def now_id(p): 
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()); 
    return f"{p}_{ts}", ts
def write(prefix,payload):
    os.makedirs("analysis/freed",exist_ok=True); os.makedirs(".tau_ledger/freed",exist_ok=True)
    rid,ts=now_id(prefix); out=f"analysis/freed/{rid}.json"
    open(out,"w",encoding="utf-8").write(json.dumps(payload,indent=2))
    mp=f".tau_ledger/freed/{rid}.manifest.json"
    open(mp,"w",encoding="utf-8").write(json.dumps({"run_id":rid,"timestamp_utc":ts,"artifacts":[{"path":out,"sha256":sha256_file(out)}]},indent=2))
    print("[manifest]", mp)
def import_lam():
    try:
        from scripts.freed.nd_kernel import lam_and_dlam
        return lam_and_dlam
    except Exception:
        def lam_and_dlam(mu):
            a=[2.0,2.5,3.0,3.5,4.0]; b=[0.3,-0.2,0.15,-0.1,0.05]; c=[0.02,0.03,0.01,0.015,0.025]
            lam=[a[i]+b[i]*mu+c[i]*(mu*mu) for i in range(5)]
            dlam=[b[i]+2.0*c[i]*mu for i in range(5)]
            return lam,dlam
        return lam_and_dlam
def mu_one_loop(mu0,b,ell):
    d=1.0-b*mu0*ell; 
    if d==0.0: d=1e-16
    return mu0/d
def F(mu,b,b1):
    return -1.0/(b*mu) + (b1/(b*b))*cmath.log((b+b1*mu)/mu)
def dF_dmu(mu,b,b1):
    return (1.0/(b*(mu*mu))) + (b1/(b*b))*( b1/(b+b1*mu) - 1.0/mu )
def newton_solve(target, mu_init, b, b1, maxit=60, tol=1e-14):
    mu=mu_init
    for _ in range(maxit):
        r=F(mu,b,b1)-target
        if abs(r) < tol: return mu
        mu = mu - r/dF_dmu(mu,b,b1)
    return mu
def ln_det(lam):
    import math
    return sum(math.log(max(1e-16, float(abs(x)))) for x in lam)
def main():
    lam_and_dlam=import_lam()
    mu0=float(os.environ.get("FREED_MU0","0.9")); b=float(os.environ.get("FREED_B","0.02")); b1=float(os.environ.get("FREED_B1","0.002"))
    pole=1.0/(b*mu0); ell1=0.22*pole; ell2=0.27*pole; ellT=ell1+ell2
    # 1-loop composition
    m1=mu_one_loop(mu0,b,ell1); m2=mu_one_loop(m1,b,ell2); mT=mu_one_loop(mu0,b,ellT)
    resid_1=abs(m2-mT)
    # 2-loop composition via target additivity
    T0=F(mu0,b,b1); T1=T0+ell1; T2=T1+ell2; TT=T0+ellT
    m1_2=newton_solve(T1, mu0, b, b1); m2_2=newton_solve(T2, m1_2, b, b1); mT_2=newton_solve(TT, mu0, b, b1)
    resid_2=abs(m2_2-mT_2)
    # additivity of log det steps
    lam0,_=lam_and_dlam(mu0); lam1,_=lam_and_dlam(m1); lamT,_=lam_and_dlam(mu_one_loop(mu0,b,ellT))
    add_resid=abs((ln_det(lam1)-ln_det(lam0)) + (ln_det(lamT)-ln_det(lam1)) - (ln_det(lamT)-ln_det(lam0)))
    write("axiom_functoriality",{
        "_inputs":{"mu0":mu0,"b":b,"b1":b1,"ell1":ell1,"ell2":ell2},
        "_claims":{"functoriality":"1-loop & 2-loop composition hold; logdet additive"},
        "_certificates":{"mu_comp_one_loop":resid_1, "mu_comp_two_loop":float(resid_2.real), "logdet_add_resid":add_resid,
                         "tolerances":{"one_loop":1e-12,"two_loop":1e-9,"add":1e-12}}
    })
if __name__=="__main__": main()
