import os, math, time, json, hashlib
from typing import List, Dict
try:
    from scripts.freed.nd_kernel import lam_and_dlam
except Exception as e:
    # minimal fallback: inline lam model
    def lam_and_dlam(mu: float):
        a=[2.0,2.5,3.0,3.5,4.0]; b=[0.3,-0.2,0.15,-0.1,0.05]; c=[0.02,0.03,0.01,0.015,0.025]
        lam=[a[i]+b[i]*mu+c[i]*mu*mu for i in range(5)]
        dlam=[b[i]+2.0*c[i]*mu for i in range(5)]
        for i in range(5):
            if lam[i]<=1e-9: lam[i]=1e-9
        return lam,dlam

def sha256_file(path: str) -> str:
    h=hashlib.sha256()
    with open(path,"rb") as f:
        for chunk in iter(lambda: f.read(1<<20), b""):
            h.update(chunk)
    return h.hexdigest()

def gm(v: List[float]) -> float:
    p=1.0
    for x in v: p*=x
    return p**(1.0/len(v))

def eta_term_report() -> Dict:
    # Weyl group orders
    W_orders={"B5": 3840, "E6": 51840}
    eta = {k: 0.5*math.log(v) for k,v in W_orders.items()}
    # spectral snapshots
    mus=[0.9, 1.1]
    snaps=[]
    for mu in mus:
        lam,_=lam_and_dlam(mu)
        lams=sorted(lam)
        g=gm(lams)
        snaps.append({
            "mu": mu,
            "lam_sorted": lams,
            "logdet": sum(math.log(x) for x in lams),
            "shape_norm": [x/g for x in lams]
        })
    return {"eta_half_logW": eta, "snapshots": snaps}

def main() -> None:
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    run_id=f"eta_tmf_{ts}"
    rep=eta_term_report()
    out=f"analysis/freed/{run_id}.json"
    with open(out,"w") as f: json.dump(rep,f,indent=2)
    mani={
        "run_id": run_id,
        "timestamp_utc": ts,
        "certificates": {
            "eta_half_logW_B5": rep["eta_half_logW"]["B5"],
            "eta_half_logW_E6": rep["eta_half_logW"]["E6"]
        },
        "artifacts":[{"path": out, "sha256": sha256_file(out)}],
        "claims":{"weyl_group_correction": "stack cardinality correction recorded alongside spectra"}
    }
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w") as f: json.dump(mani,f,indent=2)
    print("[manifest]", mp)

if __name__=="__main__": main()
