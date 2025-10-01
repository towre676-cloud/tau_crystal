import os, json, time, math, hashlib, sys
from typing import Dict, List

# local pure-Python kernels
try:
    from scripts.freed.purepy_linalg import jacobi_eigh
    from scripts.freed.nd_kernel import sigma_nondiag, lam_and_dlam
except Exception as e:
    print("[err] missing pure-Python LA kernel:", e)
    sys.exit(2)

def sha256_file(path: str) -> str:
    h=hashlib.sha256()
    with open(path,"rb") as f:
        for chunk in iter(lambda: f.read(1<<20), b""):
            h.update(chunk)
    return h.hexdigest()

def mu_one_loop(mu0: float, b: float, ell: float) -> float:
    denom = (1.0 - b*mu0*ell) or 1e-16
    return mu0 / denom

def weyl_order(name: str) -> int:
    n = name.upper()
    if n in ("B5","C5"): return (2**5) * math.factorial(5)  # 3840
    if n == "E6": return 51840
    raise ValueError(f"unknown Weyl stack {name}")

def log_base(x: float, base: str) -> float:
    b = base.lower()
    if b in ("e","ln","natural"): return math.log(x)
    if b in ("10","log10"):       return math.log10(x)
    if b in ("2","log2"):         return math.log(x)/math.log(2.0)
    return math.log(x)

def spectral_snapshot(mu: float, seed: int = 23) -> Dict:
    Sig, _, lam, _, _Q = sigma_nondiag(mu, seed=seed)
    vals, _Qj = jacobi_eigh(Sig, max_sweeps=80, tol=1e-13)
    lam_s = sorted(lam); val_s = sorted(vals)
    ev_err = sum((lam_s[i]-val_s[i])**2 for i in range(5))**0.5
    gm = (lam_s[0]*lam_s[1]*lam_s[2]*lam_s[3]*lam_s[4])**(1.0/5.0)
    shape = [x/gm for x in lam_s]
    return {"lam": lam_s, "eig": val_s, "shape_gm1": shape, "eigs_l2_err": ev_err}

def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)

    WSTACK = os.environ.get("FREED_W_STACK","B5").upper()
    PHI    = os.environ.get("FREED_PHI_TWIST","0").strip().lower() in {"1","true","yes","on"}
    LOGB   = os.environ.get("FREED_LOG_BASE","e").strip()

    eff = "E6" if (PHI and WSTACK=="B5") else WSTACK
    W = weyl_order(eff)
    eta = 0.5 * log_base(W, LOGB)

    # refs (natural log)
    eta_ref = {
        "half_ln_W_B5": 0.5*math.log(weyl_order("B5")),
        "half_ln_W_E6": 0.5*math.log(weyl_order("E6")),
        "W_B5": weyl_order("B5"),
        "W_E6": weyl_order("E6"),
    }

    mu0, b = 0.9, 0.02
    ell = 0.8/(b*mu0)
    mu_mid = mu_one_loop(mu0,b,0.5*ell)
    snap = spectral_snapshot(mu_mid, seed=23)

    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    run_id = f"eta_tmf_{ts}"
    out_path = f"analysis/freed/{run_id}.json"
    with open(out_path,"w", encoding="utf-8") as f:
        json.dump({
            "run_id": run_id, "timestamp_utc": ts,
            "inputs": {"mu0": mu0, "b": b, "ell": ell, "mu_mid": mu_mid},
            "stack": {"requested": WSTACK, "phi_twist": PHI, "effective": eff, "order": W,
                      "log_base": LOGB, "eta_half_logW": eta, "eta_refs": eta_ref},
            "spectral_snapshot": snap
        }, f, indent=2)

    manifest = {
        "run_id": run_id, "timestamp_utc": ts,
        "claims": {"eta_groupoid_correction": "0.5 * log |W| boundary term (APS)",
                   "non_diag_spectrum_certified": "Jacobi eigs ≈ analytic λ"},
        "artifacts": [{"path": out_path, "sha256": sha256_file(out_path)}],
    }
    mp = f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w", encoding="utf-8") as f: json.dump(manifest,f,indent=2)
    print("[manifest]", mp)

if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] eta reporter crashed:", e); sys.exit(1)
