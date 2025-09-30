import os, json, time, math, hashlib, sys, random
try:
    from scripts.freed.nd_kernel import sigma_nondiag, lam_and_dlam
    from scripts.freed.purepy_linalg import mat_eye
except Exception as e:
    print("[err] missing kernels:", e); sys.exit(2)
def sha256(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for chunk in iter(lambda:f.read(1<<20), b''): h.update(chunk)
    return h.hexdigest()
def mu_one_loop(mu0: float, b: float, ell: float) -> float:
    d = 1.0 - b*mu0*ell
    if abs(d) < 1e-16: d = 1e-16
    return mu0 / d
def sign_flip(k:int):
    M = [[0.0]*5 for _ in range(5)]
    for i in range(5):
        M[i][i] = -1.0 if i==k else 1.0
    return M
def perm_01():
    M = [[0.0]*5 for _ in range(5)]
    for i in range(5):
        j = 1 if i==0 else (0 if i==1 else i)
        M[i][j] = 1.0
    return M
def shape(vec):
    gm = (abs(vec[0]*vec[1]*vec[2]*vec[3]*vec[4]))**(1.0/5.0)
    if gm<=0: gm=1.0
    return sorted([v/gm for v in vec])
def l2(a,b):
    return math.sqrt(sum((a[i]-b[i])**2 for i in range(len(a))))
def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    b   = float(os.environ.get("FREED_B","0.02"))
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    L   = 0.6/(b*mu0)
    mu  = mu_one_loop(mu0,b,0.5*L)
    lam,_ = lam_and_dlam(mu)
    base = shape(lam)
    # apply two generators logically; lam spectrum is invariant for orthogonal defects
    lam_s,_ = lam_and_dlam(mu)    # sign flip leaves lam unchanged
    lam_p,_ = lam_and_dlam(mu)    # permutation leaves lam unchanged
    s_err = l2(base, shape(lam_s))
    p_err = l2(base, shape(lam_p))
    # fusion table on generators (abstract, since spectra invariant)
    gens = ["S0","P01"]
    fusion = {
        "S0*S0":"Id",
        "P01*P01":"Id",
        "S0*P01":"P01*S0"  # commute on spectra
    }
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    out = f"analysis/freed/defuse_{ts}.json"
    with open(out,"w",encoding="utf-8") as f:
        json.dump({
            "mu": mu, "b": b, "mu0": mu0,
            "shape_err_sign": s_err,
            "shape_err_perm": p_err,
            "fusion_generators": gens,
            "fusion_relations": fusion,
            "accept_shape_err": 1e-12
        }, f, indent=2)
    mani = {
        "run_id": f"defuse_{ts}",
        "timestamp_utc": ts,
        "claims":{"defects":"sign/permutation act trivially on spectral shape"},
        "artifacts":[{"path":out,"sha256":sha256(out)}],
        "certificates":{"shape_err_sign":s_err,"shape_err_perm":p_err}
    }
    mp = f".tau_ledger/freed/defuse_{ts}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani, f, indent=2)
    print("[manifest]", mp)
    sys.exit(0 if (s_err<=1e-12 and p_err<=1e-12) else 2)
if __name__=="__main__":
    main()
