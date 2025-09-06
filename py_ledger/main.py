from __future__ import annotations
import argparse, json, hashlib, numpy as np
from pathlib import Path
from .cheby_tau import chebyshev_tau
from .rank_kernel import modular_rank_with_trace
from .manifest import serialize_manifest

def _lap1d(n: int) -> np.ndarray:
    A = np.zeros((n,n), dtype=float)
    for i in range(n):
        A[i,i]=2.0
        if i>0: A[i,i-1]=-1.0
        if i+1<n: A[i,i+1]=-1.0
    return A

def _digest(A: np.ndarray) -> str:
    return hashlib.sha256(A.astype(float, copy=False).tobytes(order="C")).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--matrix", type=str, default=None)
    ap.add_argument("--n", type=int, default=64)
    ap.add_argument("--k", type=int, default=48)
    ap.add_argument("--slope_window", type=int, default=4)
    ap.add_argument("--out", type=str, default="manifest.json")
    ap.add_argument("--run_id", type=str, default="demo")
    args = ap.parse_args()

    if args.matrix:
        A = np.load(args.matrix).astype(float, copy=False)
    else:
        A = _lap1d(args.n)
    n = A.shape[0]
    v0 = np.random.default_rng(7).standard_normal(n)
    tau_series = chebyshev_tau(A, v0, k_max=args.k, slope_window=args.slope_window)
    rank_report = modular_rank_with_trace(np.rint(A * 1024.0).astype(np.int64))
    manifest = serialize_manifest(
        run_id=args.run_id,
        matrix_digest_hex=_digest(A),
        tau_series=tau_series,
        rank_report=rank_report,
        qcro_trace=[],
        params={"k_max":args.k,"slope_window":args.slope_window,
                "rank_primes": list(rank_report.get("rank_over_primes",{}).keys())},
    )
    Path(args.out).write_text(json.dumps(manifest, indent=2))
    print(f"[ok] wrote {args.out} sha256={manifest['manifest_sha256']}")

if __name__ == "__main__":
    main()
