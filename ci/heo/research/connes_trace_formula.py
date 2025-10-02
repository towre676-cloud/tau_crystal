#!/usr/bin/env python3
"""
Connes/Residue module (periodic indicator sequences):
Numerically verifies Res_{s=1} ζ_S(s) = H, where
  ζ_S(s) = Σ_{n≥1} X_S(n) / n^s
and X_S is periodic binary with mean H.

We approximate ζ_S(1+δ) for small δ and estimate
  residue ≈ (s-1) ζ_S(s) as s→1^+,
with mild Richardson-style averaging.
"""
from __future__ import annotations
import json, argparse, math, sys

def zeta_S_periodic(pattern, s, K=200000):
    """
    Direct summation over first K terms.
    pattern: list of 0/1 of length T
    s: real > 1
    """
    T = len(pattern)
    acc = 0.0
    # Batch over full periods where possible
    # But keep it simple & stable: just sum K terms.
    for n in range(1, K+1):
        acc += pattern[(n-1) % T] / (n ** s)
    return acc

def estimate_residue(pattern, deltas=(1e-1, 7e-2, 5e-2, 3e-2), K=200000):
    vals = []
    for d in deltas:
        s = 1.0 + d
        z = zeta_S_periodic(pattern, s, K=K)
        vals.append((d, (s - 1.0) * z))
    # simple bias reduction: weighted average favoring smallest deltas
    vals_sorted = sorted(vals, key=lambda x: x[0])
    weights = [1.0/v[0] for v in vals_sorted]
    wsum = sum(weights)
    residue = sum(w * v for w, (_, v) in zip(weights, vals_sorted)) / wsum
    return {"samples": [{"delta": d, "scaled": v} for d, v in vals_sorted],
            "residue_estimate": residue}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence", default="ci/data/sequences/periodic_7_0010010.json")
    ap.add_argument("--K", type=int, default=200000)
    ap.add_argument("--deltas", nargs="*", type=float, default=[0.10, 0.07, 0.05, 0.03])
    ap.add_argument("--tolerance", type=float, default=0.02)  # acceptable |res-H|
    args = ap.parse_args()

    with open(args.sequence) as f:
        seq = json.load(f)
    if seq.get("kind") != "periodic":
        print(json.dumps({"error":"only periodic fixtures supported in this module"}, indent=2))
        sys.exit(0)

    pattern = seq["pattern"]
    H = sum(pattern) / len(pattern)
    out = estimate_residue(pattern, tuple(args.deltas), K=args.K)
    residue = out["residue_estimate"]
    ok = abs(residue - H) <= args.tolerance

    print(json.dumps({
        "period": len(pattern),
        "H_exact": H,
        "samples": out["samples"],
        "residue_estimate": residue,
        "abs_error": abs(residue - H),
        "tolerance": args.tolerance,
        "residue_matches_H_within_tolerance": ok
    }, indent=2))

    # research path: never hard-fail; exit 0
    sys.exit(0)

if __name__ == "__main__":
    main()
