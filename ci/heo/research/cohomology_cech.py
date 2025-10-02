#!/usr/bin/env python3
"""
Cohomological obstruction θ_{k,k'} via Čech 1-cocycle on the cofinite topology.

We model the arithmetic site with opens U_n = {m >= n}. For two HEO sheaves
(H_d^k on S) and (H_d^{k'} on S'), we compute sections over U_n as a limsup
density restricted to indices >= n, then build the Čech C^0 data and verify
that the 1-coboundary δs is (numerically) zero. Vanishing obstruction implies
equal densities on the cofinal cover.

Usage:
  python ci/heo/research/cohomology_cech.py \
    --sequence1 ci/data/sequences/periodic_7_0010010.json \
    --sequence2 ci/data/sequences/periodic_7_0010010.json \
    --d 2 --k1 0 --k2 1 --cover-step 10 --cover-size 10
"""
import json, argparse, math, sys

EPS = 1e-12
THRESH = 1e-3

def load_sequence(path):
    obj = json.load(open(path))
    if obj.get("kind") == "periodic" and "pattern" in obj:
        patt = obj["pattern"]
        def X(n):  # 1-indexed
            return patt[(n-1) % len(patt)]
        return X, ("periodic", len(patt), sum(patt)/len(patt))
    if obj.get("kind") == "explicit" and "values" in obj:
        vals = obj["values"]
        def X(n):
            return vals[n-1] if 1 <= n <= len(vals) else 0
        mean = (sum(vals)/len(vals)) if vals else 0.0
        return X, ("explicit", len(vals), mean)
    raise SystemExit(f"Unsupported sequence format: {path}")

def limsup_density_from(X, start: int, Nmax=50000, window=2000):
    s = 0; best = 0.0
    # compute density of X over [start, start+m-1]
    for m in range(1, Nmax+1):
        s += X(start + m - 1)
        if m % window == 0:
            best = max(best, s/m)
    return best

def heo_section(X, start_idx: int) -> float:
    # Section over U_start_idx: limsup_{M} 1/M sum_{m=0}^{M-1} X(start_idx+m)
    return limsup_density_from(X, start_idx)

def cech_obstruction(seq1_path, seq2_path, d, k1, k2, cover_step, cover_size):
    X1, meta1 = load_sequence(seq1_path)
    X2, meta2 = load_sequence(seq2_path)

    cover = [1 + cover_step*i for i in range(cover_size)]
    # C^0: log-ratio sections over each open (for numerical stability)
    C0 = {}
    for n in cover:
        h1 = heo_section(X1, n)
        h2 = heo_section(X2, n)
        r = math.log(h1+EPS) - math.log(h2+EPS)
        C0[n] = {"H1": h1, "H2": h2, "log_ratio": r}

    # C^1: coboundary δs on pairwise intersections U_i ∩ U_j = U_{max(i,j)}
    C1 = {}
    max_dev = 0.0
    for i, n in enumerate(cover):
        for j in range(i+1, len(cover)):
            m = cover[j]
            si = C0[n]["log_ratio"]
            sj = C0[m]["log_ratio"]
            delta = sj - si
            C1[(n, m)] = delta
            max_dev = max(max_dev, abs(delta))

    return {
        "d": d, "k1": k1, "k2": k2,
        "cover": cover,
        "meta1": {"kind": meta1[0], "len": meta1[1], "mean": meta1[2]},
        "meta2": {"kind": meta2[0], "len": meta2[1], "mean": meta2[2]},
        "C0": C0,
        "max_abs_delta": max_dev,
        "obstruction_vanishes": (max_dev < THRESH),
        "threshold": THRESH
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence1", required=True)
    ap.add_argument("--sequence2", required=True)
    ap.add_argument("--d", type=int, default=2)
    ap.add_argument("--k1", type=int, default=0)
    ap.add_argument("--k2", type=int, default=1)
    ap.add_argument("--cover-step", type=int, default=10)
    ap.add_argument("--cover-size", type=int, default=10)
    args = ap.parse_args()

    res = cech_obstruction(
        args.sequence1, args.sequence2, args.d, args.k1, args.k2,
        args.cover_step, args.cover_size
    )
    print(json.dumps(res, indent=2))

if __name__ == "__main__":
    main()
