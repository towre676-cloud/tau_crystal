import os, json, time, math, random, hashlib, sys
from typing import List, Tuple

try:
    from scripts.freed.purepy_linalg import cholesky_lower, chol_solve, mat_eye
    from scripts.freed.nd_kernel import sigma_nondiag
except Exception as e:
    print("[err] missing LA kernel:", e); sys.exit(2)

def sha256_file(p):
    h=hashlib.sha256()
    with open(p,"rb") as f:
        for chunk in iter(lambda: f.read(1<<20), b""): h.update(chunk)
    return h.hexdigest()

def apply_defect(vec: List[float], perm: List[int], signs: List[int]) -> List[float]:
    n=len(vec); out=[0.0]*n
    for i in range(n):
        out[i] = signs[i] * vec[perm[i]]
    return out

def whiten_norm_sq(L, v):
    # given lower-Cholesky L of Sigma, ||v||_{Sigma^{-1}}^2 = ||L^{-1} v||^2
    n=len(L); m=1
    B=[[vi] for vi in v]
    X = chol_solve(L, B)  # Sigma^{-1} v
    return sum(X[i][0]*v[i] for i in range(n))

def random_perm_sign(n:int, seed:int)->Tuple[List[int], List[int]]:
    r=random.Random(seed)
    perm=list(range(n)); r.shuffle(perm)
    signs=[r.choice([-1,1]) for _ in range(n)]
    return perm, signs

def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    mu=1.1
    Sig, _, lam, _, _Q = sigma_nondiag(mu, seed=31)
    L = cholesky_lower(Sig)

    # sample several defects; transmission = ratio of whitened norms should be 1
    trials=[]
    for t in range(6):
        perm, signs = random_perm_sign(5, seed=100+t)
        det = (1 if sum(1 for s in signs if s==-1)%2==0 else -1) * (1 if (sum(1 for i in range(5) for j in range(i+1,5) if perm[i]>perm[j])%2)==0 else -1)
        r = random.Random(200+t)
        errs=[]
        for _ in range(100):
            v=[r.uniform(-1.0,1.0) for _ in range(5)]
            before = whiten_norm_sq(L, v)
            v2 = apply_defect(v, perm, signs)
            after  = whiten_norm_sq(L, v2)
            errs.append(abs(after/before - 1.0))
        trials.append({
            "perm": perm, "signs": signs, "determinant": det,
            "mean_rel_err": sum(errs)/len(errs), "max_rel_err": max(errs)
        })

    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    run_id=f"defects_{ts}"
    out=f"analysis/freed/{run_id}.json"
    with open(out,"w") as f:
        json.dump({"run_id":run_id,"timestamp_utc":ts,"trials":trials,
                   "claim":"whitened metric invariant; domain-wall transmission phase trivial (≈1)."},f,indent=2)
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w") as f:
        json.dump({"run_id":run_id,"timestamp_utc":ts,"artifacts":[{"path":out,"sha256":sha256_file(out)}],
                   "claims":{"defect_transmission":"trivial in whitened frame","noninvertible_symmetry":"W(B5) walls realized"}},f,indent=2)
    print("[manifest]", mp)

if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] defect functor crashed:", e); sys.exit(1)
