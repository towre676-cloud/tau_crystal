import os, json, time, hashlib, sys
def sha256(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for ch in iter(lambda:f.read(1<<20), b''): h.update(ch)
    return h.hexdigest()
def mu_one_loop(mu0,b,ell):
    d = 1.0 - b*mu0*ell
    if d == 0.0: d = 1e-16
    return mu0/d
def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    run_id = f"relfun_{ts}"
    mu0 = float(os.environ.get("FREED_MU0","0.9"))
    b   = float(os.environ.get("FREED_B","0.02"))
    ell1= float(os.environ.get("FREED_ELL1","10.0"))
    ell2= float(os.environ.get("FREED_ELL2","5.0"))
    mu_12  = mu_one_loop(mu0,b,ell1+ell2)
    mu_1   = mu_one_loop(mu0,b,ell1)
    mu_1_2 = mu_one_loop(mu_1,b,ell2)
    resid = abs(mu_12 - mu_1_2)
    out = {"run_id":run_id,"inputs":{"mu0":mu0,"b":b,"ell1":ell1,"ell2":ell2},
           "mu_total":mu_12,"mu_compose":mu_1_2,"residual":resid,"pass":resid<=1e-12}
    outp = f"analysis/freed/{run_id}.json"
    with open(outp,"w",encoding="utf-8") as f: json.dump(out,f,indent=2)
    mani={"run_id":run_id,"timestamp_utc":ts,
          "claims":{"relative_functor":"mu(ell1+ell2) = mu(ell2; mu(ell1))"},
          "certificates":{"composition_residual":resid,"tolerance":1e-12},
          "artifacts":[{"path":outp,"sha256":sha256(outp)}]}
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani,f,indent=2)
    print("[manifest]", mp)
if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] rel functor crashed:", e); sys.exit(1)
