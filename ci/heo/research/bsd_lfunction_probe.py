#!/usr/bin/env python3
"""
BSD–HEO probe (lightweight):
- Approximate L(E,1) for E: y^2 = x^3 + a x + b using truncated Euler product.
- Empirically estimate HEO for S(n) = n^3 + a n + b against d=2, shift k.
This is CONDITIONAL science; outputs are for research dashboards & receipts only.
"""
import json, argparse, math, sys, time

def is_prime(n: int) -> bool:
    if n < 2: return False
    if n in (2,3): return True
    if n % 2 == 0: return False
    r = int(n**0.5)
    f = 3
    while f <= r:
        if n % f == 0: return False
        f += 2
    return True

def count_curve_points_naive(a: int, b: int, p: int) -> int:
    # Count #E(F_p) for E: y^2 = x^3 + a x + b mod p (O(p^2) — fine for small p)
    count = 1  # point at infinity
    for x in range(p):
        rhs = (x*x*x + a*x + b) % p
        # count solutions y with y^2 ≡ rhs
        # Use Legendre symbol by brute force (small p) for simplicity
        s = 0
        for y in range(p):
            if (y*y) % p == rhs:
                s += 1
        count += s
    return count

def compute_ap(a: int, b: int, p: int):
    if not is_prime(p): return None
    return p + 1 - count_curve_points_naive(a, b, p)

def euler_product_approximation(a: int, b: int, primes, s: float = 1.0) -> float:
    prod = 1.0
    for p in primes:
        if not is_prime(p): continue
        ap = compute_ap(a, b, p)
        if ap is None: continue
        # assume good reduction (χ(p)=1) for this toy probe
        denom = 1.0 - ap/(p**s) + 1.0/(p**(2.0*s - 1.0))
        # fall back if singular
        if abs(denom) < 1e-12: continue
        prod *= 1.0/denom
    return prod

def is_perfect_power(n: int, d: int) -> bool:
    if n < 0 and d % 2 == 0: return False
    if n < 0: 
        r = round((-n)**(1.0/d))
        return (-r)**d == n
    r = round(n**(1.0/d))
    return (r**d == n) or ((r+1)**d == n) or ((r-1)**d == n)

def empirical_heo_cubic(a: int, b: int, k: int, d: int = 2, Nmax: int = 5000, window: int = 250) -> dict:
    s = 0
    best = 0.0
    hits = 0
    for n in range(1, Nmax+1):
        S = n*n*n + a*n + b
        if is_perfect_power(S + k, d):
            hits += 1
        if n % window == 0:
            best = max(best, hits/n)
    return {"Nmax": Nmax, "window": window, "hits": hits, "limsup_estimate": best, "final_ratio": hits/max(Nmax,1)}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--a", type=int, default=0, help="E: y^2 = x^3 + a x + b")
    ap.add_argument("--b", type=int, default=1, help="E: y^2 = x^3 + a x + b")
    ap.add_argument("--k", type=int, default=1, help="Shift in S(n)+k = m^2")
    ap.add_argument("--primes", nargs="+", type=int, default=[2,3,5,7,11,13,17,19,23,29])
    ap.add_argument("--Nmax", type=int, default=5000)
    args = ap.parse_args()

    t0 = time.time()
    L_approx = euler_product_approximation(args.a, args.b, args.primes, s=1.0)
    t1 = time.time()
    H_emp = empirical_heo_cubic(args.a, args.b, args.k, d=2, Nmax=args.Nmax, window=max(50, args.Nmax//20))
    t2 = time.time()

    traces = {}
    for p in args.primes:
        if is_prime(p):
            ap_p = compute_ap(args.a, args.b, p)
            traces[p] = ap_p

    out = {
        "curve": {"a": args.a, "b": args.b},
        "shift_k": args.k,
        "truncated_primes": args.primes,
        "L_value_approx_at_1": L_approx,
        "frobenius_traces": traces,
        "HEO_empirical": H_emp,
        "timings_sec": {"L": round(t1-t0,4), "HEO": round(t2-t1,4)},
        "notes": "Heuristic/conditional: truncated Euler product; empirical HEO over finite prefix.",
        "bsd_predicates": {
            "analytic_rank_positive_proxy": (abs(L_approx) < 0.5),
            "bsd_predicts_H_zero": not (abs(L_approx) < 0.5)
        }
    }
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
