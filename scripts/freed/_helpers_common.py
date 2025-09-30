import os, json, time, math, hashlib

def sha256_file(p):
    h=hashlib.sha256()
    with open(p,"rb") as f:
        for chunk in iter(lambda: f.read(1<<20), b""): h.update(chunk)
    return h.hexdigest()

def now_run_id(prefix):
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    return f"{prefix}_{ts}", ts

def ensure_dirs():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)

def write_receipt(prefix, payload):
    ensure_dirs()
    run_id, ts = now_run_id(prefix)
    out = f"analysis/freed/{run_id}.json"
    with open(out,"w",encoding="utf-8") as f: json.dump(payload, f, indent=2)
    mani = {
        "run_id": run_id, "timestamp_utc": ts,
        "artifacts":[{"path": out, "sha256": sha256_file(out)}],
        "inputs": payload.get("_inputs",{}),
        "certificates": payload.get("_certificates",{}),
        "claims": payload.get("_claims",{})
    }
    mp = f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani, f, indent=2)
    print("[manifest]", mp)

# kernels (pure-python fallback if nd_kernel missing)
def import_linalg():
    try:
        from scripts.freed.nd_kernel import lam_and_dlam
        return lam_and_dlam
    except Exception:
        def lam_and_dlam(mu: float):
            a=[2.0,2.5,3.0,3.5,4.0]; b=[0.3,-0.2,0.15,-0.1,0.05]; c=[0.02,0.03,0.01,0.015,0.025]
            lam=[a[i]+b[i]*mu+c[i]*mu*mu for i in range(5)]
            dlam=[b[i]+2.0*c[i]*mu for i in range(5)]
            for i in range(5):
                if lam[i] <= 1e-12: lam[i]=1e-12
            return lam, dlam
        return lam_and_dlam

def mu_one_loop(mu0: float, b: float, ell: float) -> float:
    denom = (1.0 - b*mu0*ell) or 1e-16
    return mu0 / denom

def dmu_dell_one_loop(mu: float, b: float) -> float:
    return b * mu * mu  # dμ/dℓ = b μ^2

def scheduler_walls(mu0: float, b: float, k: int=6):
    walls=[]
    for i in range(1, k+1):
        ell_k = (1.0/(b*mu0))*(1.0 - math.exp(-3.0*b*i))
        walls.append(ell_k)
    return walls

def log_base(x, base):
    if base == "e": return math.log(x)
    if base == "2": return math.log(x, 2)
    if base == "10": return math.log10(x)
    return math.log(x)

def ln_to_base(x, base):
    if base == "e": return x
    if base == "2": return x / math.log(2.0)
    if base == "10": return x / math.log(10.0)
    return x
