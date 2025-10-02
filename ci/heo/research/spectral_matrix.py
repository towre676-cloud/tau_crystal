#!/usr/bin/env python3
import json, argparse, math
from typing import List, Tuple

def load_sequence(path: str):
    with open(path) as f:
        obj = json.load(f)
    kind = obj.get("kind","periodic")
    if kind != "periodic":
        raise ValueError("This diagnostic expects a periodic fixture with 'pattern'.")
    patt = obj["pattern"]
    T = len(patt)
    H = sum(patt)/T
    return patt, T, H

def build_cov_matrix(H: float, k_values: List[int], xi: float = 2.0) -> List[List[float]]:
    """
    Simple positive semidefinite kernel:
      Σ_{ij} = H(1-H) * exp(-|k_i - k_j| / xi)
    Gives variance H(1-H) on diagonal and exponentially decaying correlations off-diagonal.
    """
    n = len(k_values)
    Sigma = [[0.0]*n for _ in range(n)]
    for i, ki in enumerate(k_values):
        for j, kj in enumerate(k_values):
            dist = abs(ki - kj)
            corr = math.exp(-dist/xi)
            Sigma[i][j] = H*(1.0-H)*corr
    return Sigma

def matvec(A: List[List[float]], v: List[float]) -> List[float]:
    return [sum(A[i][j]*v[j] for j in range(len(v))) for i in range(len(A))]

def dot(u: List[float], v: List[float]) -> float:
    return sum(ui*vi for ui,vi in zip(u,v))

def norm(v: List[float]) -> float:
    return math.sqrt(max(0.0, dot(v,v)))

def power_iteration(A: List[List[float]], iters: int = 500, tol: float = 1e-12) -> Tuple[float, List[float]]:
    n = len(A)
    v = [1.0/n]*n
    for _ in range(iters):
        Av = matvec(A, v)
        nv = norm(Av)
        if nv < tol:
            break
        v_new = [x/nv for x in Av]
        if norm([v_new[i]-v[i] for i in range(n)]) < 1e-10:
            v = v_new
            break
        v = v_new
    Av = matvec(A, v)
    lam = dot(v, Av)
    return lam, v

def deflate(A: List[List[float]], lam: float, v: List[float]) -> None:
    n = len(A)
    for i in range(n):
        for j in range(n):
            A[i][j] -= lam * v[i] * v[j]

def top_k_eigs(A_in: List[List[float]], k: int = 5) -> Tuple[List[float], List[List[float]]]:
    # deep copy
    A = [row[:] for row in A_in]
    vals, vecs = [], []
    for _ in range(min(k, len(A))):
        lam, v = power_iteration(A)
        vals.append(lam); vecs.append(v)
        deflate(A, lam, v)
    return vals, vecs

def spectral_gap(vals: List[float]):
    if len(vals) < 2: 
        return {"gap": None, "ratio": None, "is_isolated": None}
    gap = vals[0] - vals[1]
    ratio = (vals[1]/vals[0]) if vals[0] > 0 else None
    return {"gap": gap, "ratio": ratio, "is_isolated": (gap is not None and vals[0] > 0 and gap > 0.1*vals[0])}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence", default="ci/data/sequences/periodic_7_0010010.json")
    ap.add_argument("--d", type=int, default=2)  # placeholder for interface parity
    ap.add_argument("--k-min", type=int, default=-6)
    ap.add_argument("--k-max", type=int, default=6)
    ap.add_argument("--xi", type=float, default=2.0, help="correlation length in k-space")
    ap.add_argument("--top", type=int, default=5)
    args = ap.parse_args()

    patt, T, H = load_sequence(args.sequence)
    ks = list(range(args.k_min, args.k_max+1))
    Sigma = build_cov_matrix(H, ks, xi=args.xi)
    vals, vecs = top_k_eigs(Sigma, k=args.top)
    gap = spectral_gap(vals)

    # simple derived quantities
    trace = sum(Sigma[i][i] for i in range(len(Sigma)))
    corr_len = None
    if len(vals) >= 2 and vals[0] > 0 and vals[1] > 0:
        r = vals[1]/vals[0]
        if r < 1.0:
            corr_len = -1.0/math.log(r)

    out = {
        "sequence": args.sequence,
        "period": T,
        "H": H,
        "k_range": [args.k_min, args.k_max],
        "xi": args.xi,
        "trace": trace,
        "eigenvalues_top": vals,
        "spectral_gap": gap,
        "correlation_length_est": corr_len,
        "dominant_mode": vecs[0] if vecs else None
    }
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
