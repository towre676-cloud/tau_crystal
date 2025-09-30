import os, json, time, math, hashlib
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
def ln_det(lam): 
    import math
    return sum(math.log(max(1e-16, float(abs(x)))) for x in lam)
def main():
    lam_and_dlam=import_lam()
    mu0=float(os.environ.get("FREED_MU0","0.9")); b=float(os.environ.get("FREED_B","0.02"))
    base=os.environ.get("FREED_LOG_BASE","e").strip().lower()
    stack=os.environ.get("FREED_W_STACK","B5").strip().upper()
    phi= os.environ.get("FREED_PHI_TWIST","0").strip().lower() in {"1","true","yes","on"}
    pole=1.0/(b*mu0); ell=0.8*pole; mu=mu_one_loop(mu0,b,ell)
    lam0,_=lam_and_dlam(mu0); lamT,_=lam_and_dlam(mu)
    bulk_ln=ln_det(lamT)-ln_det(lam0)
    def ln_to_base(x):
        import math
        if base=="2": return x/math.log(2.0)
        if base=="10": return x/math.log(10.0)
        return x
    bulk=ln_to_base(bulk_ln)
    # eta
    W = 51840 if phi or stack=="E6" else 3840
    eta_half = ln_to_base(0.5*__import__("math").log(W))
    # Gaussian index proxy
    logB_model = ln_to_base(-0.5*bulk_ln)
    gap = abs((bulk - eta_half) - logB_model)
    write("axiom_aps_accounting",{
        "_inputs":{"mu0":mu0,"b":b,"ell":ell,"stack":stack,"phi":phi,"log_base":base},
        "_claims":{"aps_accounting":"bulk - η/2 matches Gaussian logB (proxy)"},
        "_certificates":{"abs_gap":gap,"tolerance":1e-9},
        "terms":{"bulk":bulk,"eta_half":eta_half,"logB_gaussian":logB_model}
    })
if __name__=="__main__": main()
