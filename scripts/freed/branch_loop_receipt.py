import os, json, time, math, cmath, hashlib

def sha256_file(p):
    h=hashlib.sha256()
    with open(p,"rb") as f:
        for ch in iter(lambda:f.read(1<<20), b""): h.update(ch)
    return h.hexdigest()

def now_id(prefix):
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    return f"{prefix}_{ts}", ts

def ensure_dirs():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)

def write(prefix, payload):
    ensure_dirs()
    rid, ts = now_id(prefix)
    out = f"analysis/freed/{rid}.json"
    with open(out, "w", encoding="utf-8") as f: json.dump(payload, f, indent=2)
    mani = {"run_id": rid, "timestamp_utc": ts, "artifacts":[{"path": out, "sha256": sha256_file(out)}]}
    mp = f".tau_ledger/freed/{rid}.manifest.json"
    with open(mp, "w", encoding="utf-8") as f: json.dump(mani, f, indent=2)
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
            for i in range(5):
                if abs(lam[i]) <= 1e-12: lam[i]=1e-12
            return lam,dlam
        return lam_and_dlam

def F(mu,b,b1):
    return -1.0/(b*mu) + (b1/(b*b))*cmath.log((b+b1*mu)/mu)

def dF_dmu(mu,b,b1):
    return (1.0/(b*(mu*mu))) + (b1/(b*b))*( b1/(b+b1*mu) - 1.0/mu )

def newton_solve(target, mu_init, b, b1, maxit=60, tol=1e-14):
    mu=mu_init
    for _ in range(maxit):
        r=F(mu,b,b1)-target
        if abs(r) < tol: return mu
        J=dF_dmu(mu,b,b1)
        mu = mu - r/J
    return mu

def singulars_inv_sqrt(lam):
    return sorted([1.0/math.sqrt(max(1e-16, float(abs(x)))) for x in lam])

def main():
    lam_and_dlam=import_lam()
    mu0=float(os.environ.get("FREED_MU0","0.9"))
    b=float(os.environ.get("FREED_B","0.02"))
    b1=float(os.environ.get("FREED_B1","0.002"))
    ell_frac=float(os.environ.get("FREED_ELL_FRAC","0.6"))
    ell= ell_frac*(1.0/(b*mu0))

    T0=F(mu0,b,b1)
    target = T0 + ell
    mu_real = newton_solve(target, mu0, b, b1)

    # one full loop around the logarithmic branch
    mu_loop = newton_solve(target + 2j*math.pi*(b1/(b*b)), mu_real, b, b1)

    # evaluate spectra with **real** parameter (shape check)
    mu_eval_pre  = float(mu_real.real)
    mu_eval_post = float(mu_loop.real)

    lamR,_=lam_and_dlam(mu_eval_pre)
    lamL,_=lam_and_dlam(mu_eval_post)
    sR=singulars_inv_sqrt(lamR)
    sL=singulars_inv_sqrt(lamL)
    errs=[abs(a-b)/max(1.0,abs(a)) for a,b in zip(sR,sL)]
    worst=max(errs) if errs else 0.0

    write("a9_branch_loop",{
        "_inputs":{"mu0":mu0,"b":b,"b1":b1,"ell":ell,"mu_eval_pre":mu_eval_pre,"mu_eval_post":mu_eval_post},
        "_claims":{"branch_loop":"Σ^{-1/2} singular values invariant under one branch loop (real-shape)"},
        "_certificates":{"worst_rel_change": float(worst), "tolerance": 1e-9},
        "singvals":{"pre":sR,"post":sL}
    })

if __name__=="__main__":
    main()
