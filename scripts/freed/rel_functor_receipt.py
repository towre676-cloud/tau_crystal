import os, json, time, hashlib, math, sys
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
    # pick two segments (robust to scale)
    L   = 0.6/(b*mu0)
    l1  = 0.35*L
    l2  = 0.65*L
    direct = mu_one_loop(mu0, b, l1+l2)
    staged = mu_one_loop(mu_one_loop(mu0, b, l1), b, l2)
    resid  = abs(direct - staged)
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    out = f"analysis/freed/relfun_{ts}.json"
    with open(out,"w",encoding="utf-8") as f:
        json.dump({
            "b": b, "mu0": mu0, "l1": l1, "l2": l2,
            "mu_direct": direct, "mu_staged": staged,
            "composition_abs_resid": resid,
            "accept_threshold_1loop": 1e-12
        }, f, indent=2)
    mani = {
        "run_id": f"relfun_{ts}",
        "timestamp_utc": ts,
        "artifacts": [{"path": out, "sha256": sha256(out)}],
        "claims": {"rel_functor": "1-loop composition checked"},
        "certificates": {"composition_abs_resid": resid}
    }
    mp = f".tau_ledger/freed/relfun_{ts}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani, f, indent=2)
    print("[manifest]", mp)
    # gate
    sys.exit(0 if resid <= 1e-12 else 2)
if __name__=="__main__":
    main()
