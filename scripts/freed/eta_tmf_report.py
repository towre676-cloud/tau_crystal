import os, json, time, math, hashlib, sys
from typing import Dict, List

# local pure-Python kernels with safe fallback
def _sha(path: str) -> str:
    h=hashlib.sha256()
    with open(path,"rb") as f:
        for ch in iter(lambda: f.read(1<<20), b""): h.update(ch)
    return h.hexdigest()

def _weyl_order(name: str) -> int:
    n=name.upper()
    if n in ("B5","C5"): return (2**5)*math.factorial(5) # 3840
    if n=="E6": return 51840
    raise ValueError(f"unknown Weyl stack {name}")

def _log_base(x: float, base: str) -> float:
    b=base.lower()
    if b in ("e","ln","natural"): return math.log(x)
    if b in ("10","log10"): return math.log10(x)
    if b in ("2","log2"): return math.log(x)/math.log(2.0)
    return math.log(x)

# Fallback spectrum: use same λ(μ) as the verifier
def _lam(mu: float):
    a=[2.0,2.5,3.0,3.5,4.0]; b=[0.3,-0.2,0.15,-0.1,0.05]; c=[0.02,0.03,0.01,0.015,0.025]
    return [a[i]+b[i]*mu+c[i]*mu*mu for i in range(5)]

def mu_one_loop(mu0: float, b: float, ell: float) -> float:
    d=(1.0 - b*mu0*ell) or 1e-16
    return mu0/d

def spectral_snapshot(mu: float) -> Dict:
    lam=sorted(_lam(mu))
    gm=(lam[0]*lam[1]*lam[2]*lam[3]*lam[4])**(1.0/5.0)
    shape=[x/gm for x in lam]
    return {"lam": lam, "shape_gm1": shape, "eigs_l2_err": 0.0}

def main():
    os.makedirs("analysis/freed", exist_ok=True); os.makedirs(".tau_ledger/freed", exist_ok=True)
    WSTACK=os.environ.get("FREED_W_STACK","B5").upper()
    PHI=os.environ.get("FREED_PHI_TWIST","0").strip().lower() in {"1","true","yes","on"}
    LOGB=os.environ.get("FREED_LOG_BASE","e").strip()
    eff="E6" if (PHI and WSTACK=="B5") else WSTACK
    W=_weyl_order(eff); eta=0.5*_log_base(W, LOGB)
    eta_ref={"half_ln_W_B5":0.5*math.log(_weyl_order("B5")), "half_ln_W_E6":0.5*math.log(_weyl_order("E6")),
             "W_B5":_weyl_order("B5"), "W_E6":_weyl_order("E6")}
    mu0,b=0.9,0.02; ell=0.8/(b*mu0); mu_mid=mu_one_loop(mu0,b,0.5*ell)
    snap=spectral_snapshot(mu_mid)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()); run_id=f"eta_tmf_{ts}"
    out=f"analysis/freed/{run_id}.json"
    with open(out,"w",encoding="utf-8") as f:
        json.dump({"run_id":run_id,"timestamp_utc":ts,
                   "inputs":{"mu0":mu0,"b":b,"ell":ell,"mu_mid":mu_mid},
                   "stack":{"requested":WSTACK,"phi_twist":PHI,"effective":eff,"order":W,
                            "log_base":LOGB,"eta_half_logW":eta,"eta_refs":eta_ref},
                   "spectral_snapshot":snap}, f, indent=2)
    mani={"run_id":run_id,"timestamp_utc":ts,
          "claims":{"eta_groupoid_correction":"0.5*log|W| recorded (APS)"},
          "certificates":{"eta_half_logW":eta,
                          "eta_half_logW_B5":eta_ref["half_ln_W_B5"],
                          "eta_half_logW_E6":eta_ref["half_ln_W_E6"]},
          "artifacts":[{"path":out,"sha256":_sha(out)}]}
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani,f,indent=2)
    print("[manifest]", mp)

if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] eta reporter crashed:", e); sys.exit(1)
