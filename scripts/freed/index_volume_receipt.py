import os, json, time, math, hashlib, sys
try:
    from scripts.freed.nd_kernel import lam_and_dlam
except Exception as e:
    print("[err] missing nd_kernel:", e); sys.exit(2)
def sha256(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for chunk in iter(lambda:f.read(1<<20), b''): h.update(chunk)
    return h.hexdigest()
def mu_one_loop(mu0: float, b: float, ell: float) -> float:
    d = 1.0 - b*mu0*ell
    if abs(d) < 1e-16: d = 1e-16
    return mu0 / d
def half_logW(phi: bool, base: str)->float:
    w = 51840 if phi else 3840
    return 0.5*(math.log10(w) if base=="10" else math.log(w))
def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    b   = float(os.environ.get("FREED_B","0.02"))
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    phi = os.environ.get("FREED_PHI_TWIST","0").strip().lower() in {"1","true","yes","on"}
    base= os.environ.get("FREED_LOG_BASE","e").strip().lower()
    L   = 0.6/(b*mu0)
    μ    = mu_one_loop(mu0,b,0.5*L)
    lam,_ = lam_and_dlam(μ)
    logVol = -0.5*sum(math.log(max(x,1e-18)) for x in lam)  # Gaussian model vs identity null
    corr  = - half_logW(phi, base)                           # stack correction
    idx   = logVol + corr
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    out = f"analysis/freed/indexvol_{ts}.json"
    with open(out,"w",encoding="utf-8") as f:
        json.dump({
            "b": b, "mu0": mu0, "phi_twist": phi, "log_base": base,
            "mid_mu": μ, "logGaussianVolume_model_vs_null": logVol,
            "stack_correction": corr, "relative_index_estimate": idx
        }, f, indent=2)
    mani = {
        "run_id": f"indexvol_{ts}",
        "timestamp_utc": ts,
        "claims":{"relative_index":"Gaussian volume + stack correction"},
        "artifacts":[{"path":out,"sha256":sha256(out)}],
        "certificates":{"index_estimate": idx}
    }
    mp = f".tau_ledger/freed/indexvol_{ts}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani, f, indent=2)
    print("[manifest]", mp)
    sys.exit(0)
if __name__=="__main__":
    main()
