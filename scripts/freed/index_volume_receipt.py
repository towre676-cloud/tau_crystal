import os, json, time, math, hashlib, sys
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
def sha256(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for ch in iter(lambda:f.read(1<<20), b''): h.update(ch)
    return h.hexdigest()
def main():
    os.makedirs("analysis/freed",exist_ok=True)
    os.makedirs(".tau_ledger/freed",exist_ok=True)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()); run_id=f"indexvol_{ts}"
    mu0=float(os.environ.get("FREED_MU0","0.9")); b=float(os.environ.get("FREED_B","0.02"))
    L=float(os.environ.get("FREED_ELL","12.0"))
    mu=mu_one_loop(mu0,b,L)
    lam,_=lam_and_dlam(mu)
    logdet=sum(math.log(x) for x in lam)
    log_vol_ratio = -0.5*logdet
    logW=math.log(3840.0)  # |W(B5)|
    log_vol_ratio_stack = log_vol_ratio - 0.5*logW
    out={"run_id":run_id,"inputs":{"mu0":mu0,"b":b,"L":L},
         "logdet":logdet,"log_vol_ratio_model_vs_null":log_vol_ratio,
         "logW_B5":logW,"stack_corrected_log_volume":log_vol_ratio_stack}
    outp=f"analysis/freed/{run_id}.json"
    with open(outp,"w",encoding="utf-8") as f: json.dump(out,f,indent=2)
    mani={"run_id":run_id,"timestamp_utc":ts,
          "claims":{"relative_index_volume":"logB ~ log Vol(model/null) on stack quotient"},
          "artifacts":[{"path":outp,"sha256":sha256(outp)}]}
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani,f,indent=2)
    print("[manifest]", mp)
if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] index volume crashed:", e); sys.exit(1)
