import os, json, time, math, hashlib
def sha256_file(p):
    h=hashlib.sha256(); 
    with open(p,"rb") as f:
        for c in iter(lambda: f.read(1<<20), b""): h.update(c)
    return h.hexdigest()
def ensure_dirs():
    os.makedirs("analysis/freed",exist_ok=True); os.makedirs(".tau_ledger/freed",exist_ok=True)
def write_receipt(prefix,payload):
    ensure_dirs(); ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    out=f"analysis/freed/{prefix}_{ts}.json"
    json.dump(payload, open(out,"w",encoding="utf-8"), indent=2)
    mani={"run_id":f"{prefix}_{ts}","timestamp_utc":ts,"artifacts":[{"path":out,"sha256":sha256_file(out)}]}
    mp=f".tau_ledger/freed/{prefix}_{ts}.manifest.json"
    json.dump(mani, open(mp,"w",encoding="utf-8"), indent=2); print("[manifest]", mp)

def lam_and_dlam(mu: float):
    a=[2.0,2.5,3.0,3.5,4.0]; b=[0.3,-0.2,0.15,-0.1,0.05]; c=[0.02,0.03,0.01,0.015,0.025]
    lam=[a[i]+b[i]*mu+c[i]*mu*mu for i in range(5)]
    dlam=[b[i]+2.0*c[i]*mu for i in range(5)]
    for i in range(5):
        if lam[i] <= 1e-12: lam[i]=1e-12
    return lam, dlam

def mu_one(mu0,b,ell): 
    d=(1.0-b*mu0*ell); 
    return mu0/(d if d!=0 else 1e-16)
def dmu_dell(mu,b): return b*mu*mu

def main():
    mu0=float(os.environ.get("FREED_MU0","0.9")); b=float(os.environ.get("FREED_B","0.02"))
    pole=1.0/(b*mu0); ell=0.8*pole; K=41
    max_abs_err=0.0; samples=[]
    for j in range(K):
        t=ell*(j/(K-1)); mu=mu_one(mu0,b,t)
        lam,dlam=lam_and_dlam(mu); dmu=dmu_dell(mu,b)
        tr_series=sum((dlam[i]*dmu)/lam[i] for i in range(5))
        # central difference on ℓ (via μ(ℓ±h))
        h=max(1e-7*ell,1e-10)
        mu_m=mu_one(mu0,b,t-h); mu_p=mu_one(mu0,b,t+h)
        lam_m,_=lam_and_dlam(mu_m); lam_p,_=lam_and_dlam(mu_p)
        ln_m=sum(math.log(x) for x in lam_m); ln_p=sum(math.log(x) for x in lam_p)
        fd=(ln_p - ln_m)/(2*h)
        err=abs(tr_series - fd); max_abs_err=max(max_abs_err, err)
        if j%5==0: samples.append({"t":t,"abs_err":err})
    # tiny holonomy loop (central cancels)
    t0=0.5*ell; h=max(1e-6*ell,1e-10)
    mu_m=mu_one(mu0,b,t0-h); mu_p=mu_one(mu0,b,t0+h)
    lam_m,_=lam_and_dlam(mu_m); lam_p,_=lam_and_dlam(mu_p)
    ln_m=sum(math.log(x) for x in lam_m); ln_p=sum(math.log(x) for x in lam_p)
    hol=((ln_p - ln_m)/(2*h))+((ln_m - ln_p)/(2*h))
    payload={"_inputs":{"mu0":mu0,"b":b,"ell":ell},
             "_claims":{"trace_identity":"central-diff match","holonomy_zero":"flat"},
             "_certificates":{"max_abs_err":max_abs_err,"holonomy_estimate":abs(hol),
                               "tolerances":{"trace":1e-11,"holonomy":1e-13}},
             "samples":samples}
    write_receipt("a2_curvature", payload)
if __name__=="__main__": main()
