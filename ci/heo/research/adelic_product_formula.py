#!/usr/bin/env python3
import json, argparse, math
from typing import List, Dict

def poly_mod(a: List[int], n: int, mod: int) -> int:
    # a[i] * n^i (mod mod)
    acc = 0
    p = 1
    for ai in a:
        acc = (acc + (ai % mod) * p) % mod
        p = (p * (n % mod)) % mod
    return acc

def dth_powers_mod(p: int, N: int, d: int) -> Dict[int, int]:
    """Return a dict counting how many m produce each residue r ≡ m^d (mod p^N)."""
    mod = p**N
    cnt = {}
    for m in range(mod):
        r = pow(m, d, mod)
        cnt[r] = cnt.get(r, 0) + 1
    return cnt

def local_density_polynomial(coeffs: List[int], k: int, d: int, p: int, N_max: int = 5):
    """
    For S(n)=sum a_i n^i, compute densities ρ_p(N) = (1/p^N) #{n mod p^N : S(n)+k ≡ m^d (mod p^N)}.
    """
    dens = []
    for N in range(1, N_max + 1):
        mod = p**N
        powers = dth_powers_mod(p, N, d)
        count = 0
        for n in range(mod):
            target = (poly_mod(coeffs, n, mod) + k) % mod
            if target in powers:
                count += 1
        dens.append(count / mod)
    # return limsup estimate (use max of tail to be robust)
    tail = dens[-min(3, len(dens)):]
    return {"p": p, "densities": dens, "H_p": max(tail)}

def adelic_product(coeffs: List[int], k: int, d: int, primes: List[int], N_max: int = 5):
    locals_info = [local_density_polynomial(coeffs, k, d, p, N_max) for p in primes]
    # use uniform weights for a baseline
    w = 1.0 / max(1, len(locals_info))
    # avoid log(0)
    eps = 1e-12
    # global proxy: min of locals (upper bound heuristic)
    H_global_proxy = min(max(li["H_p"], eps) for li in locals_info)
    log_global = math.log(H_global_proxy)
    log_weighted = sum(w * math.log(max(li["H_p"], eps)) for li in locals_info)
    return {
        "coeffs": coeffs, "k": k, "d": d,
        "primes": primes, "N_max": N_max,
        "locals": locals_info,
        "H_global_proxy": H_global_proxy,
        "log_global_proxy": log_global,
        "weighted_log_locals": log_weighted,
        "abs_error": abs(log_global - log_weighted),
        "holds_loose": abs(log_global - log_weighted) < 0.5
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--coeffs", nargs="+", type=int, required=True, help="Polynomial coeffs a0 a1 ... ar (S(n)=Σ a_i n^i)")
    ap.add_argument("--k", type=int, default=1)
    ap.add_argument("--d", type=int, default=2)
    ap.add_argument("--primes", nargs="+", type=int, default=[2,3,5,7,11])
    ap.add_argument("--N-max", type=int, default=5)
    args = ap.parse_args()
    res = adelic_product(args.coeffs, args.k, args.d, args.primes, args.N_max)
    print(json.dumps(res, indent=2))

if __name__ == "__main__":
    main()
