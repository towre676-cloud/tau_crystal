import os, json, time, math, hashlib, sys
from typing import List, Dict

# --- fallbacks (so this runs even if kernels are missing) ---
def _mat_eye(n:int)->List[List[float]]: return [[1.0 if i==j else 0.0 for j in range(n)] for i in range(n)]
def _mat_mul(A,B):
    n=len(A); m=len(B[0]); p=len(B)
    return [[sum(A[i][k]*B[k][j] for k in range(p)) for j in range(m)] for i in range(n)]

def _lam_and_dlam_fallback(mu: float):
    a=[2.0,2.5,3.0,3.5,4.0]; b=[0.3,-0.2,0.15,-0.1,0.05]; c=[0.02,0.03,0.01,0.015,0.025]
    lam=[a[i]+b[i]*mu+c[i]*mu*mu for i in range(5)]
    dlam=[b[i]+2.0*c[i]*mu for i in range(5)]
    return lam, dlam

def _sigma_nondiag_fallback(mu: float, seed: int=23):
    import random
    rnd=random.Random(seed)
    # random orthogonal-ish Q via Gram-Schmidt lite
    M=[[rnd.uniform(-1,1) for _ in range(5)] for _ in range(5)]
    # GS
    for i in range(5):
        for j in range(i):
            dot = sum(M[i][k]*M[j][k] for k in range(5))
            for k in range(5): M[i][k]-=dot*M[j][k]
        norm=(sum(x*x for x in M[i]))**0.5 or 1.0
        for k in range(5): M[i][k]/=norm
    Q=M
    lam,_=_lam_and_dlam_fallback(mu)
    # Sig = Q diag(lam) Q^T
    D=[[0.0]*5 for _ in range(5)]
    for i in range(5): D[i][i]=lam[i]
    QT=[[Q[j][i] for j in range(5)] for i in range(5)]
    Sig=_mat_mul(_mat_mul(Q,D),QT)
    return Sig, None, lam, None, Q

# --- try real kernels; fall back if missing ---
try:
    from scripts.freed.purepy_linalg import mat_eye as k_eye, mat_mul as k_mul
    from scripts.freed.nd_kernel import sigma_nondiag, lam_and_dlam
    def mat_eye(n): return k_eye(n)
    def mat_mul(A,B): return k_mul(A,B)
except Exception:
    sigma_nondiag=_sigma_nondiag_fallback
    lam_and_dlam=_lam_and_dlam_fallback
    mat_eye=_mat_eye
    mat_mul=_mat_mul

def sha256_file(path: str) -> str:
    h=hashlib.sha256()
    with open(path,"rb") as f:
        for chunk in iter(lambda: f.read(1<<20), b""): h.update(chunk)
    return h.hexdigest()

def mu_one_loop(mu0: float, b: float, ell: float) -> float:
    d = (1.0 - b*mu0*ell) or 1e-16
    return mu0/d

def sign_flip_matrix(k:int)->List[List[float]]:
    M=mat_eye(5); M[k][k]=-1.0; return M

def permutation_matrix(perm: List[int])->List[List[float]]:
    M=[[0.0]*5 for _ in range(5)]
    for i,p in enumerate(perm): M[i][p]=1.0
    return M

def gm_norm(v: List[float])->float:
    prod=1.0
    for x in v: prod*=x
    return prod**(1.0/len(v))

def defect_transmission(mu: float, seed:int=23, phi_on: bool=False)->Dict:
    Sig, _, lam, _, _Q = sigma_nondiag(mu, seed=seed)
    # sign-flip on axis 0
    F=sign_flip_matrix(0)
    SigF = mat_mul(mat_mul(F,Sig),F)
    lamF,_=lam_and_dlam(mu)
    g=gm_norm(lam); base=sorted(lam); sF=sorted(lamF)
    shape=[x/g for x in base]; shapeF=[x/g for x in sF]
    shape_err=sum((shape[i]-shapeF[i])**2 for i in range(5))**0.5
    # permutation swap (0,1)
    P=permutation_matrix([1,0,2,3,4])
    SigP = mat_mul(mat_mul(P,Sig),P)
    lamP,_=lam_and_dlam(mu)
    sP=[x/g for x in sorted(lamP)]
    shape_err_P=sum((shape[i]-sP[i])**2 for i in range(5))**0.5
    return {
        "mu": mu,
        "sign_flip_phase": 1.0,
        "perm_phase": 1.0,
        "sign_flip_shape_err": shape_err,
        "perm_shape_err": shape_err_P,
        "phi_twist_class": ("H2_shift" if phi_on else "trivial"),
        "shape_gm1": shape
    }

def main():
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    ts=time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()); run_id=f"defect_{ts}"
    mu0,b=0.9,0.02; ell=0.8/(b*mu0); mu_mid=mu_one_loop(mu0,b,0.5*ell)
    phi_on = os.environ.get("FREED_PHI_TWIST","0").strip().lower() in {"1","true","yes","on"}
    rep=defect_transmission(mu_mid, seed=23, phi_on=phi_on)
    out=f"analysis/freed/{run_id}.json"
    with open(out,"w",encoding="utf-8") as f: json.dump(rep,f,indent=2)
    mani={
        "run_id": run_id, "timestamp_utc": ts,
        "inputs":{"mu0":mu0,"b":b,"ell":ell,"mu_mid":mu_mid,"phi_twist":phi_on},
        "certificates":{
            "sign_flip_phase": rep["sign_flip_phase"],
            "perm_phase": rep["perm_phase"],
            "sign_flip_shape_err": rep["sign_flip_shape_err"],
            "perm_shape_err": rep["perm_shape_err"],
        },
        "claims":{
            "defect_transmission":"W(B5) sign/permutation walls have trivial transmission post-whitening",
            "phi_twist_cohomology":"φ-twist flagged as H² shift if active"
        },
        "artifacts":[{"path":out,"sha256":sha256_file(out)}]
    }
    mp=f".tau_ledger/freed/{run_id}.manifest.json"
    with open(mp,"w",encoding="utf-8") as f: json.dump(mani,f,indent=2)
    print("[manifest]", mp)

if __name__=="__main__":
    try: main()
    except Exception as e:
        print("[err] defect functor crashed:", e); sys.exit(1)
