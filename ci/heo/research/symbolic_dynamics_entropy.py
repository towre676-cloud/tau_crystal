#!/usr/bin/env python3
"""
Symbolic dynamics analysis for binary periodic X:
- Block entropy h_n = (1/n) log_2(# distinct blocks of length n)
- Topological entropy h_top ≈ lim_{n→∞} h_n  (zero for periodic)
- Kolmogorov complexity proxy via zlib compression
"""
from __future__ import annotations
import json, argparse, math, zlib, sys

def compute_block_counts(pattern, max_length=12, repeat=16):
    # Extend pattern to improve statistics
    seq = (pattern * repeat)
    Lseq = len(seq)
    counts = {}
    for n in range(1, max_length + 1):
        seen = set()
        for i in range(Lseq):
            blk = tuple(seq[(i + j) % Lseq] for j in range(n))
            seen.add(blk)
        counts[n] = len(seen)
    return counts

def entropies_from_counts(counts):
    Hn = {}
    for n, cnt in counts.items():
        if cnt <= 0:
            Hn[n] = 0.0
        else:
            Hn[n] = math.log2(cnt) / n
    return Hn

def estimate_h_top(Hn):
    if not Hn:
        return 0.0
    keys = sorted(Hn.keys())
    tail = keys[-3:] if len(keys) >= 3 else keys
    return sum(Hn[k] for k in tail) / len(tail)

def kolmogorov_rate(pattern, repeat=64):
    seq = bytes((pattern * repeat))
    comp = zlib.compress(seq, level=9)
    if len(seq) == 0:
        return {"original_len": 0, "compressed_len": len(comp), "ratio": 0.0, "K_rate_bits_per_symbol": 0.0}
    ratio = len(comp) / len(seq)
    # rough proxy: bits per symbol
    return {
        "original_len": len(seq),
        "compressed_len": len(comp),
        "ratio": ratio,
        "K_rate_bits_per_symbol": ratio * 8.0
    }

def analyze(sequence_path, max_block_len=12):
    with open(sequence_path) as f:
        obj = json.load(f)
    if obj.get("kind") != "periodic":
        return {"error": "only periodic fixtures supported"}
    pattern = obj["pattern"]
    H = sum(pattern) / len(pattern)

    counts = compute_block_counts(pattern, max_length=max_block_len)
    Hn = entropies_from_counts(counts)
    h_top = estimate_h_top(Hn)
    Kproxy = kolmogorov_rate(pattern)

    return {
        "period": len(pattern),
        "H_mean": H,
        "block_counts": counts,
        "h_n": Hn,
        "h_top_estimate": h_top,
        "kolmogorov_proxy": Kproxy,
        "verifications": {
            "periodic_entropy_is_zero": h_top < 1e-9 + 1e-6,  # numerical floor
            "compression_small": Kproxy["K_rate_bits_per_symbol"] < 1.0  # heuristic for periodicity
        }
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence", default="ci/data/sequences/periodic_7_0010010.json")
    ap.add_argument("--max-block-length", type=int, default=12)
    args = ap.parse_args()
    res = analyze(args.sequence, args.max_block_length)
    print(json.dumps(res, indent=2))
    # research job is non-blocking
    sys.exit(0)

if __name__ == "__main__":
    main()
