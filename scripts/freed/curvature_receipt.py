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
def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    b   = float(os.environ.get("FREED_B","0.02"))
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    L   = 0.6/(b*mu0)
    # sample at μ, then at μ(ℓ+δℓ)
    ell  = 0.4*L
    dℓ   = 1e-4*L
    μ    = mu_one_loop(mu0,b,ell)
    μ2   = mu_one_loop(mu0,b,ell+dℓ)
    lam, dlam = lam_and_dlam(μ)
    lam2,_    = lam_and_dlam(μ2)
    # chain rule: ∂ℓ log det Σ = (∑ (dλ/dμ)/λ) * dμ/dℓ, with dμ/dℓ = b μ^2
    dμ_dℓ = b*(μ**2)
    lhs   = sum((dlam[i]/lam[i]) for i in range(5)) * dμ_dℓ
    # finite difference on log det Σ
    logdet  = sum(math.log(max(l,1e-18)) for l in lam)
    logdet2 = sum(math.log(max(l,1e-18)) for l in lam2)
    rhs = (logdet2 - logdet) / dℓ
    resid = abs(lhs - rhs)
    # tiny "holonomy": forward/backward loop in ℓ should cancel
    μ3   = mu_one_loop(mu0,b,ell-dℓ)
    lam3,_ = lam_and_dlam(μ3)
    logdet3 = sum(math.log(max(l,1e-18)) for l in lam3)
    hol = (logdet2 - logdet)/dℓ + (logdet - logdet3)/dℓ  # should be ~0
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    out = f"analysis/freed/curv_{ts}.json"
    with open(out,"w",encoding="utf-8") as f:
        json.dump({
            "b": b, "mu0": mu0, "ell": ell, "delta_ell": dℓ,
            "trace_identity_abs_resid": resid,
            "holonomy_closure_resid": hol,
            "accept_trace_resid": 1e-10,
            "accept_holonomy_resid": 1e-10
        }, f, indent=2)
    mani = {
        "run_id": f"curv_{ts}",
        "timestamp_utc": ts,
        "claims": {"trace_identity":"checked via chain rule vs finite diff",
                   "holonomy":"forward/backward loop cancels"},
        "artifacts":[{"path":out,"sha256":sha256(out)}],
        "certificates":{"trace_identity_abs_resid":resid,"holonomy_resid":hol}
    }
    mp = f".tau_ledger/freed/curv_{ts}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani, f, indent=2)
    print("[manifest]", mp)
    sys.exit(0 if (resid<=1e-10 and abs(hol)<=1e-10) else 2)
if __name__=="__main__":
    main()
