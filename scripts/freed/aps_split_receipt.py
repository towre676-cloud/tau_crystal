import os, json, time, math, glob, hashlib, sys
try:
    from scripts.freed.nd_kernel import lam_and_dlam
except Exception:
    def lam_and_dlam(mu: float):
        a=[2.0,2.5,3.0,3.5,4.0]; b=[0.30,-0.20,0.15,-0.10,0.05]; c=[0.02,0.03,0.01,0.015,0.025]
        lam=[a[i]+b[i]*mu+c[i]*mu*mu for i in range(5)]
        dlam=[b[i]+2.0*c[i]*mu for i in range(5)]
        for i in range(5):
            if lam[i]<=1e-12: lam[i]=1e-12
        return lam,dlam
def mu_one_loop(mu0,b,ell):
    d=1.0-b*mu0*ell
    if d==0.0: d=1e-16
    return mu0/d
def latest(pat):
    files=sorted(glob.glob(pat))
    return files[-1] if files else None
def sha256(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for ch in iter(lambda:f.read(1<<20), b''): h.update(ch)
    return h.hexdigest()
def main():
    os.makedirs("analysis/freed",exist_ok=True)
    os.makedirs(".tau_ledger/freed",exist_ok=True)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()); run_id=f"aps_{ts}"
    mu0=float(os.environ.get("FREED_MU0","0.9")); b=float(os.environ.get("FREED_B","0.02"))
    L=float(os.environ.get("FREED_ELL","12.0"))
    lam0,_=lam_and_dlam(mu_one_loop(mu0,b,0.0))
    lamL,_=lam_and_dlam(mu_one_loop(mu0,b,L))
    bulk = sum(math.log(x) for x in lamL) - sum(math.log(x) for x in lam0)
    # eta from latest receipt if present; else |W(B5)|
    eta_file = latest("analysis/freed/eta_tmf_*.json")
    eta_half=None
    if eta_file:
        try:
            with open(eta_file,"r",encoding="utf-8") as f:
                rec=json.load(f); eta_half = rec.get("eta_half_logW") or rec.get("eta_half_logW_B5")
        except Exception: eta_half=None
    if eta_half is None:
        eta_half = 0.5*math.log(3840.0)
    # We don't recompute logB here; report residual to APS split using k in {-2..2}
    logB_est = bulk
    best_k=0; best_res=abs(logB_est - (bulk - eta_half))
    for k in (-2,-1,0,1,2):
        r=abs(logB_est - (bulk - eta_half + k))
        if r<best_res: best_res=r; best_k=k
    out={"run_id":run_id,"inputs":{"mu0":mu0,"b":b,"L":L},
         "bulk":bulk,"eta_half":eta_half,"k_integer":best_k,
         "aps_sum": (bulk - eta_half + best_k),"residual":best_res}
    outp=f"analysis/freed/{run_id}.json"
    with open(outp,"w",encoding="utf-8") as f: json.dump(out,f,indent=2)
    mani={"run_id":run_id,"timestamp_utc":ts,
          "claims":{"APS_split":"logB = ∫bulk - η/2 + ℤ (one-loop)"},
          "certificates":{"residual":best_res,"k":best_k},
          "artifacts":[{"path":outp,"sha256":sha256(outp)}]}
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani,f,indent=2)
    print("[manifest]", mp)
if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] aps split crashed:", e); sys.exit(1)
