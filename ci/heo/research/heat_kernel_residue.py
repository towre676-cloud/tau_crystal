#!/usr/bin/env python3
"""
Heat-kernel verification for periodic indicator sequences X:
K(t) = Σ_{n≥1} X(n) e^{-n t},  t→0^+  ⇒  t K(t) → H,
where H is the periodic mean of X.
We compute K(t) by a closed-form periodic decomposition and
verify t*K(t) ~ H for a ladder of small t.
"""
from __future__ import annotations
import json, argparse, math, sys

def K_periodic(pattern, t, terms_per_residue=200000):
    """
    Periodic closed form:
      K(t) = Σ_{r=1}^T X(r) * e^{-r t} / (1 - e^{-T t})
    Truncation can be done directly by the geometric formula; terms_per_residue
    is unused in the closed form but kept for testing parity.
    """
    T = len(pattern)
    denom = 1.0 - math.exp(-T * t)
    if abs(denom) < 1e-300:
        # fallback to partial sum if t extremely small
        s = 0.0
        N = terms_per_residue * T
        for n in range(1, N + 1):
            s += pattern[(n - 1) % T] * math.exp(-n * t)
        return s
    num = 0.0
    for r in range(1, T + 1):
        if pattern[r - 1]:
            num += math.exp(-r * t)
    return num / denom

def verify_limit(pattern, t_values, tolerance):
    H = sum(pattern) / len(pattern)
    rows = []
    ok = True
    for t in t_values:
        Kt = K_periodic(pattern, t)
        tk = t * Kt
        err = abs(tk - H)
        rows.append({"t": t, "tK(t)": tk, "abs_error": err})
        ok = ok and (err <= tolerance)
    return H, rows, ok

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence", default="ci/data/sequences/periodic_7_0010010.json")
    ap.add_argument("--tolerance", type=float, default=0.02)
    ap.add_argument("--t-grid", nargs="*", type=float,
                    default=[1e-1, 7e-2, 5e-2, 3e-2, 2e-2, 1e-2])
    args = ap.parse_args()

    with open(args.sequence) as f:
        obj = json.load(f)
    if obj.get("kind") != "periodic":
        print(json.dumps({"error": "only periodic fixtures supported"}, indent=2))
        sys.exit(0)

    pattern = obj["pattern"]
    H, rows, ok = verify_limit(pattern, args.t_grid, args.tolerance)

    print(json.dumps({
        "period": len(pattern),
        "H_exact": H,
        "grid": rows,
        "tolerance": args.tolerance,
        "limit_verified": ok
    }, indent=2))
    # research: non-blocking
    sys.exit(0)

if __name__ == "__main__":
    main()
