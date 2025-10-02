import math, itertools as it, numpy as np
from fractions import Fraction

def alpha(mu):
    aMZ_inv, aTau_inv = 127.955, 133.476
    MZ, mTau = 91.1876, 1.77686
    mu = max(min(mu, MZ), mTau)
    b = (aTau_inv - aMZ_inv) / math.log(mTau/MZ)
    inv = aMZ_inv + b*math.log(mu/MZ)
    return 1.0/inv

def alpha_s(mu):
    nf, aMZ = 5, 0.1180
    beta0 = 11.0 - 2.0*nf/3.0
    L = MZ = 91.1876
    ln_MZ_over_L = (2*math.pi)/(beta0*aMZ)
    L = MZ/math.exp(ln_MZ_over_L)
    mu = max(mu, L*1.0001)
    return 4*math.pi/(beta0*math.log((mu/L)**2))

PI = math.pi
PHI = (1+5**0.5)/2
mp_me = 938.27208816/0.51099895

mus = np.exp(np.linspace(math.log(2.0), math.log(200.0), 21))
wts = np.ones_like(mus)/len(mus)

def basis(mu):
    return np.array([math.log(alpha(mu)), math.log(alpha_s(mu)), math.log(PI), math.log(PHI), math.log(mp_me)], float)

Xc = sum(w*basis(w) for w in mus)/len(mus)
S = np.zeros((5,5))
for w in mus:
    d = basis(w)-Xc
    S += np.outer(d,d)/len(mus)
evals, evecs = np.linalg.eigh(S + 1e-18*np.eye(5))
W = evecs @ np.diag(1.0/np.sqrt(np.maximum(evals,1e-18))) @ evecs.T

def Xw(mu): return W @ (basis(mu)-Xc)

nums = [-5,-3,-2,-1,1,2,3,5]; dens = [1,2,3,5,12,18,30]
ALPH = sorted({Fraction(n,d) for n in nums for d in dens}, key=float)
phi_idx = 3

def rg_error(r, logR):
    se = 0.0
    for mu, wt in zip(mus, wts): se += wt*(logR - float(np.dot(r, Xw(mu))))**2
    return se

def bic_like(r):
    nz = [i for i,v in enumerate(r) if abs(v)>1e-15]
    s = len(nz)
    denom = sum(Fraction(r[i]).limit_denominator().denominator for i in nz)
    return 0.5*s*math.log(len(mus)) + 1e-3*denom

log_lambda_phi = -2.0
def objective(r, logR):
    return rg_error(r, logR) + bic_like(r) + (0 if abs(r[phi_idx])<1e-15 else -log_lambda_phi)

def canon_B5(r):
    v = np.array([0 if abs(x)<1e-15 else x for x in r], float)
    order = sorted(range(5), key=lambda i:(-abs(v[i]), -np.sign(v[i])))
    w = v[order]
    for i in range(5):
        if abs(w[i])>1e-15:
            if w[i] < 0: w = -w
            break
    return tuple(float(np.round(x,12)) for x in w)

def search(logR, maxk=3):
    best = {}
    for k in range(1, maxk+1):
        for Spt in it.combinations(range(5), k):
            for exps in it.product(ALPH, repeat=k):
                r = np.zeros(5, float)
                for i,e in zip(Spt, exps): r[i] = float(e)
                key = canon_B5(r)
                val = objective(r, logR)
                if key not in best or val < best[key][0]: best[key] = (val, r)
    return sorted(best.values(), key=lambda t:t[0])

if __name__ == "__main__":
    tau_e = 1776.93/0.51099895
    ranked = search(math.log(tau_e), maxk=3)
    val, r = ranked[0]
    print("best_val", val); print("best_raw", np.round(r, 12)); print("best_canon", canon_B5(r))
