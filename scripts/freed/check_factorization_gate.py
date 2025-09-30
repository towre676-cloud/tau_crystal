import glob, json, sys, os
def latest(pat):
    xs = sorted(glob.glob(pat))
    return xs[-1] if xs else None
def load(p):
    with open(p,"r",encoding="utf-8") as f: return json.load(f)
def extract_resid(d):
    # try common keys
    for k in ["residual","abs_resid","abs_err","error","factorization_abs_err"]:
        if k in d: return abs(d[k])
    # nested?
    for k in d:
        v=d[k]
        if isinstance(v,dict):
            r=extract_resid(v)
            if r is not None: return r
    return None
def main():
    rtol = float(os.environ.get("GATE_FACT_RTOL","1e-9"))
    off = latest("analysis/freed/*_factorization_phi_off.json")
    on  = latest("analysis/freed/*_factorization_phi_on.json")
    if not off or not on:
        print("[err] missing factorization receipts"); sys.exit(3)
    roff = extract_resid(load(off))
    ron  = extract_resid(load(on))
    if roff is None or ron is None:
        print("[err] cannot extract residuals"); sys.exit(4)
    ok = (roff <= rtol) and (ron <= rtol)
    print("[gate] factorization phi-off resid=", roff, " phi-on resid=", ron, " rtol=", rtol)
    sys.exit(0 if ok else 2)
if __name__=="__main__":
    main()
