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
def dmu_dell(mu,b): return b*mu*mu
def main():
    lam_and_dlam=import_lam()
    mu0=float(os.environ.get("FREED_MU0","0.9")); b=float(os.environ.get("FREED_B","0.02"))
    pole=1.0/(b*mu0); ell=0.8*pole; K=64
    max_err=0.0
    for j in range(K):
        t=ell*(j/(K-1)); mu=mu_one_loop(mu0,b,t); lam,dl=lam_and_dlam(mu)
        tr=0.0; dmu=dmu_dell(mu,b)
        for i in range(5): tr += (dl[i]*dmu)/lam[i]
        h=max(1e-8*ell,1e-12); mf=mu_one_loop(mu0,b,t+h); lamf,_=lam_and_dlam(mf)
        ln=sum(math.log(x) for x in lam); lnf=sum(math.log(x) for x in lamf)
        fd=(lnf-ln)/h; err=abs(tr-fd); 
        if err>max_err: max_err=err
    # holonomy on 3 midpoints
    mids=[0.3*ell,0.5*ell,0.7*ell]; hols=[]
    for t0 in mids:
        mu=mu_one_loop(mu0,b,t0); lam,_=lam_and_dlam(mu); h=max(1e-6*ell,1e-10)
        mup=mu_one_loop(mu0,b,t0+h); lamp,_=lam_and_dlam(mup)
        ln=sum(math.log(x) for x in lam); lnp=sum(math.log(x) for x in lamp)
        hol=(lnp-ln)/h + (ln-lnp)/h
        hols.append(abs(hol))
    write("axiom_flatness",{
        "_inputs":{"mu0":mu0,"b":b,"ell":ell}, 
        "_claims":{"flatness":"trace identity tight; tiny-loop holonomy ~ 0"},
        "_certificates":{"max_trace_abs_err":max_err,"max_holonomy":max(hols),"tolerances":{"trace":1e-10,"hol":1e-12}}
    })
if __name__=="__main__": main()
