#!/usr/bin/env python3
"""
Grover Search Planner for HEO hits.

Given a 0/1 indicator sequence X(n) (periodic or explicit fixture) and a search
space size N, compute:
  - t = # { 1 <= n <= N : X(n) = 1 }  (marked items)
  - optimal Grover iteration count r (rounded)
  - success probability after r iterations
  - classical vs quantum query complexities and speedup factor

This is dependency-light and does NOT require qiskit. If you pass --qiskit and
qiskit is installed, the script will *report* availability but does not execute
heavy quantum sims in CI.
"""
import json, argparse, math, importlib.util, sys
from typing import Dict, Any

def load_indicator(path: str):
    with open(path) as f:
        obj = json.load(f)
    kind = obj.get("kind")
    if kind == "periodic":
        patt = obj["pattern"]
        T = len(patt)
        def X(n: int) -> int:
            return int(patt[(n-1) % T])
        return X, {"kind":"periodic","period":T,"H":sum(patt)/T}
    elif kind == "explicit":
        vals = obj["values"]
        L = len(vals)
        def X(n: int) -> int:
            if 1 <= n <= L:
                return int(vals[n-1])
            return 0
        H = sum(vals)/max(L,1)
        return X, {"kind":"explicit","length":L,"H":H}
    else:
        raise ValueError("Unsupported sequence kind; expected 'periodic' or 'explicit'.")

def grover_plan(N: int, t: int) -> Dict[str, Any]:
    if N <= 0:
        return {"t": t, "r_opt": 0, "success_prob": 0.0, "classical_avg": 0.0, "grover_queries": 0.0, "speedup": None, "theta": None}
    if t <= 0:
        # No marked items: Grover not applicable
        return {"t": 0, "r_opt": 0, "success_prob": 0.0,
                "classical_avg": float("inf"), "grover_queries": 0.0,
                "speedup": 0.0, "theta": 0.0}
    # Standard parameterization
    a = math.sqrt(t / N)                    # amplitude of marked subspace
    theta = math.asin(a)                    # Grover rotation angle
    # Heuristic near-optimal iteration count
    r = max(0, int(round((math.pi/(4*theta)) - 0.5)))
    success = math.sin((2*r + 1)*theta)**2
    classical = N / t                       # expected classical queries
    grover_q = (math.pi/4)*math.sqrt(N / t) # asymptotic optimal queries
    speedup = classical / grover_q
    return {
        "t": t,
        "r_opt": r,
        "success_prob": success,
        "classical_avg": classical,
        "grover_queries": grover_q,
        "speedup": speedup,
        "theta": theta
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence", default="ci/data/sequences/periodic_7_0010010.json")
    ap.add_argument("--N", type=int, default=512, help="search space size")
    ap.add_argument("--d", type=int, default=2)  # placeholder for interface parity
    ap.add_argument("--k", type=int, default=0)  # placeholder
    ap.add_argument("--qiskit", action="store_true", help="report qiskit availability")
    args = ap.parse_args()

    X, meta = load_indicator(args.sequence)
    # Count hits in 1..N
    t = sum(X(n) for n in range(1, args.N+1))
    plan = grover_plan(args.N, t)

    # Optional: check for qiskit presence (no heavy run)
    qiskit_available = False
    if args.qiskit:
        qiskit_available = importlib.util.find_spec("qiskit") is not None

    out = {
        "sequence": args.sequence,
        "meta": meta,
        "N": args.N,
        "hits_t": t,
        "plan": plan,
        "qiskit_available": qiskit_available,
        "notes": "This planner uses closed-form Grover estimates; no quantum backend is required."
    }
    print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
