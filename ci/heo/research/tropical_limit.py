#!/usr/bin/env python3
"""
Tropical HEO limit:
    H_trop := lim_{t->0+} t * log( sum_{n=1}^N exp(X(n)/t) )

For binary X(n) ∈ {0,1}, Laplace's principle gives:
    H_trop = max_n X(n) ∈ {0,1}.

We compute a numerically stable approximation using log-sum-exp, report the
convergence over a decreasing grid of t's, and compare to max X.
"""
import json, argparse, math, sys
from typing import Tuple, List

def load_indicator(path: str):
    with open(path) as f:
        obj = json.load(f)
    kind = obj.get("kind")
    if kind == "periodic":
        patt = obj["pattern"]
        T = len(patt)
        def X(n: int) -> int:
            return int(patt[(n-1) % T])
        return X, ("periodic", {"period": T, "H": sum(patt)/T})
    elif kind == "explicit":
        vals = obj["values"]
        L = len(vals)
        def X(n: int) -> int:
            if 1 <= n <= L:
                return int(vals[n-1])
            return 0
        H = sum(vals)/max(L,1)
        return X, ("explicit", {"length": L, "H": H})
    else:
        raise ValueError("Unsupported sequence kind; expected 'periodic' or 'explicit'.")

def stable_tropical_value(xs: List[float], t: float) -> float:
    """
    Compute t * log( sum_i exp(xs[i]/t) ) stably using log-sum-exp.
    For xs ∈ {0,1}, this is robust even for small t.
    """
    m = max(xs)
    # sum exp((x - m)/t)
    s = 0.0
    for x in xs:
        s += math.exp((x - m)/t)
    # t * (m/t + log s) = m + t * log s
    return m + t * math.log(s)

def collect_window(X, N: int) -> List[int]:
    return [int(X(n)) for n in range(1, N+1)]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence", default="ci/data/sequences/periodic_7_0010010.json")
    ap.add_argument("--N", type=int, default=2048, help="prefix length to scan")
    ap.add_argument("--t-grid", nargs="*", type=float, default=[0.5, 0.3, 0.2, 0.1, 0.07, 0.05])
    ap.add_argument("--assert", action="store_true", help="assert tropical limit equals max(X)")
    args = ap.parse_args()

    X, meta = load_indicator(args.sequence)
    window = collect_window(X, args.N)
    xmax = max(window) if window else 0

    traj = []
    for t in args.t_grid:
        val = stable_tropical_value(window, t)
        traj.append({"t": t, "tropical_value": val})

    approx_limit = traj[-1]["tropical_value"] if traj else 0.0
    ok = abs(approx_limit - xmax) <= 0.05  # loose numeric tolerance

    out = {
        "sequence": args.sequence,
        "meta": { "kind": meta[0], **meta[1] },
        "N": args.N,
        "max_X": int(xmax),
        "tropical_trace": traj,
        "approx_limit": approx_limit,
        "matches_theorem": ok,
        "theorem": "For binary X, lim_{t->0+} t log Σ e^{X/t} = max X."
    }
    print(json.dumps(out, indent=2))
    if args.assert:
        assert ok, "Tropical limit numerical check failed against max(X)."

if __name__ == "__main__":
    main()
