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
def eta_half(stack:str, base:str)->float:
    # half log |W| with base 'e' or '10'
    if stack.upper()=="B5":  w=3840
    elif stack.upper()=="E6": w=51840
    else: w=3840
    if base=="10": return 0.5*math.log10(w)
    return 0.5*math.log(w)
def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    b   = float(os.environ.get("FREED_B","0.02"))
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    base= os.environ.get("FREED_LOG_BASE","e").strip().lower()
    phi = os.environ.get("FREED_PHI_TWIST","0").strip().lower() in {"1","true","yes","on"}
    stack = "E6" if phi else "B5"
    # integrate bulk over [0,L]
    L = 0.6/(b*mu0)
    steps = 240
    bulk = 0.0
    for k in range(steps):
        a = L*k/steps
        c = L*(k+1)/steps
        m_a = mu_one_loop(mu0,b,a)
        m_c = mu_one_loop(mu0,b,c)
        lam_a,_ = lam_and_dlam(m_a)
        lam_c,_ = lam_and_dlam(m_c)
        f_a = sum(math.log(max(x,1e-18)) for x in lam_a)
        f_c = sum(math.log(max(x,1e-18)) for x in lam_c)
        bulk += (f_a+f_c)*0.5*(c-a)  # trapezoid on log det Σ
    # APS decomposition (no integer index term available here)
    ehalf = eta_half(stack, base)
    logB_aps = bulk - ehalf
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    out = f"analysis/freed/aps_{ts}.json"
    with open(out,"w",encoding="utf-8") as f:
        json.dump({
            "b": b, "mu0": mu0, "phi_twist": phi, "stack": stack, "log_base": base,
            "bulk_integral_trapz_logdetSigma": bulk,
            "eta_half_logW": ehalf,
            "logB_bulk_minus_eta": logB_aps
        }, f, indent=2)
    mani = {
        "run_id": f"aps_{ts}",
        "timestamp_utc": ts,
        "claims": {"APS":"logB ≈ ∫bulk − η/2 (index term omitted)"},
        "artifacts":[{"path":out,"sha256":sha256(out)}],
        "certificates":{"bulk":bulk,"eta_half":ehalf}
    }
    mp = f".tau_ledger/freed/aps_{ts}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani, f, indent=2)
    print("[manifest]", mp)
    sys.exit(0)
if __name__=="__main__":
    main()
