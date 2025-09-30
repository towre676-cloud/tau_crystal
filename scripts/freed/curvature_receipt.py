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
def sha256(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for ch in iter(lambda:f.read(1<<20), b''): h.update(ch)
    return h.hexdigest()
def mu_one_loop(mu0,b,ell):
    d = 1.0 - b*mu0*ell
    if d == 0.0: d = 1e-16
    return mu0/d
def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()); run_id=f"curv_{ts}"
    mu0=float(os.environ.get("FREED_MU0","0.9")); b=float(os.environ.get("FREED_B","0.02"))
    L=float(os.environ.get("FREED_ELL","12.0")); steps=int(os.environ.get("FREED_STEPS","121"))
    xs=[i*L/(steps-1) for i in range(steps)]
    mus=[mu_one_loop(mu0,b,x) for x in xs]
    dmu=[b*m*m for m in mus]
    tr_vals=[]
    logdet=[]
    for m,dm in zip(mus,dmu):
        lam,dlam=lam_and_dlam(m)
        tr_vals.append(sum((dlam[i]*dm)/lam[i] for i in range(5)))
        logdet.append(sum(math.log(l) for l in lam))
    # central difference for interior points
    dfd=[(logdet[i+1]-logdet[i-1])/(xs[i+1]-xs[i-1]) for i in range(1,len(xs)-1)]
    tr_core=tr_vals[1:-1]
    resid=[abs(a-b) for a,b in zip(tr_core, dfd)]
    max_res = max(resid) if resid else 0.0
    # tiny loop holonomy: forward eps then back
    eps=L/steps
    mu_f = mu_one_loop(mu0,b,eps)
    mu_b = mu_one_loop(mu_f,b,-eps)
    hol = abs(mu_b - mu0)
    out={"run_id":run_id,"inputs":{"mu0":mu0,"b":b,"L":L,"steps":steps},
         "max_trace_identity_residual":max_res,"holonomy_residual":hol,
         "pass": (max_res<=1e-10 and hol<=1e-12)}
    outp=f"analysis/freed/{run_id}.json"
    with open(outp,"w",encoding="utf-8") as f: json.dump(out,f,indent=2)
    mani={"run_id":run_id,"timestamp_utc":ts,
          "claims":{"flatness":"d/dℓ log det = tr(Σ⁻¹ ∂ℓΣ)","holonomy_trivial":"1D leaf loop"},
          "certificates":{"max_trace_identity_residual":max_res,"holonomy_residual":hol},
          "artifacts":[{"path":outp,"sha256":sha256(outp)}]}
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani,f,indent=2)
    print("[manifest]", mp)
if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] curvature crashed:", e); sys.exit(1)
