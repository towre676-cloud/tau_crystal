#!/usr/bin/env python3
"""
Arithmetic Hash using HEO-inspired features.

Algorithm (deterministic, stdlib-only):
  1) Build weighted integer sequence S_m from message bytes:
       S_m(n) = sum_{j<=n} m_j * p_j, where p_j is the j-th prime.
  2) For d in {2,3,5} and k in {0,1,...,K-1} (K = min(32, len(S_m))):
       H_{d,k} := (# of indices n with S_m(n)+k being a perfect d-th power) / len(S_m)
  3) XOR-fold 32-bit scalars floor(2^32 * H_{d,k}) into an accumulator.
  4) SHA-256 the 32-byte big-endian accumulator to get a 256-bit digest.

CLI:
  arith_hash.py --message "hello"
  arith_hash.py --file path.bin
  arith_hash.py --test-avalanche --message "hello" --flips 16
"""
from __future__ import annotations
import argparse, hashlib, math, sys, json
from typing import List

def primes_up_to_count(count: int) -> List[int]:
    """Return at least `count` primes via incremental sieve."""
    if count <= 0:
        return []
    # heuristic upper bound for nth prime ~ n(log n + log log n)
    # use a safe multiplier for small n
    n = max(count, 6)
    import math as _m
    upper = int(n * (_m.log(n) + _m.log(_m.log(n)) + 3))
    # sieve
    sieve = bytearray(b"\x01") * (upper + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(upper**0.5) + 1):
        if sieve[i]:
            step = i
            start = i * i
            sieve[start: upper+1: step] = b"\x00" * ((upper - start)//step + 1)
    primes = [i for i, v in enumerate(sieve) if v]
    # ensure enough primes (expand if unlucky)
    while len(primes) < count:
        # extend bound and resieve (rare)
        upper *= 2
        sieve = bytearray(b"\x01") * (upper + 1)
        sieve[0:2] = b"\x00\x00"
        for i in range(2, int(upper**0.5) + 1):
            if sieve[i]:
                sieve[i*i: upper+1: i] = b"\x00" * ((upper - i*i)//i + 1)
        primes = [i for i, v in enumerate(sieve) if v]
    return primes[:count]

def iroot(n: int, d: int) -> int:
    """Integer floor d-th root by binary search (n >= 0, d >= 2)."""
    if n < 0:
        return 0
    if n in (0, 1):
        return n
    lo, hi = 0, 1
    # expand hi until hi^d > n
    while pow(hi, d) <= n:
        hi <<= 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        p = pow(mid, d)
        if p == n:
            return mid
        if p < n:
            lo = mid
        else:
            hi = mid
    return lo

def is_dth_power(val: int, d: int) -> bool:
    if val < 0 or d < 2:
        return False
    r = iroot(val, d)
    return pow(r, d) == val

def build_weighted_sequence(message_bytes: bytes) -> List[int]:
    """S_m(n) = sum_{j<=n} m_j * p_j (primes indexed from j=1)."""
    L = len(message_bytes)
    primes = primes_up_to_count(L)
    S = []
    csum = 0
    for j, b in enumerate(message_bytes, start=1):
        csum += b * primes[j-1]
        S.append(csum)
    return S

def compute_HEO_spectrum(S: List[int], d_vals=(2,3,5), k_cap=32) -> List[int]:
    """Return list of 32-bit ints floor(2^32 * H_{d,k})."""
    N = max(len(S), 1)
    K = min(k_cap, N)
    out = []
    for d in d_vals:
        for k in range(K):
            cnt = 0
            for val in S:
                if is_dth_power(val + k, d):
                    cnt += 1
            H = cnt / N
            out.append(int((2**32) * H) & 0xFFFFFFFF)
    return out

def xor_fold_to_256bit(words32: List[int]) -> bytes:
    acc = 0
    for w in words32:
        acc ^= (w & 0xFFFFFFFF)
        # rotate-mix into 256-bit lane
        acc = ((acc << 13) | (acc >> 19)) & ((1 << 256) - 1)
        acc ^= (w << 97) & ((1 << 256) - 1)
    return acc.to_bytes(32, 'big')

def arith_hash(message: bytes) -> str:
    S = build_weighted_sequence(message)
    words = compute_HEO_spectrum(S)
    seed = xor_fold_to_256bit(words)
    return hashlib.sha256(seed).hexdigest()

def hamming_distance_hex256(h1: str, h2: str) -> int:
    x = int(h1, 16) ^ int(h2, 16)
    return x.bit_count()

def avalanche_test(message: bytes, flips: int = 16) -> dict:
    base = arith_hash(message)
    L = len(message)
    if L == 0:
        return {"error": "empty message"}
    import copy
    results = []
    msg = bytearray(message)
    # flip one bit in successive positions (wrap over length)
    for i in range(flips):
        bidx = i % L
        bit = 1 << (i % 8)
        msg[bidx] ^= bit
        h2 = arith_hash(bytes(msg))
        hd = hamming_distance_hex256(base, h2)
        results.append({"flip_index": i, "byte": bidx, "bit": i % 8, "hamming": hd})
        # revert bit
        msg[bidx] ^= bit
    avg = sum(r["hamming"] for r in results) / max(len(results), 1)
    return {
        "base_hash": base,
        "results": results,
        "average_hamming": avg,
        "ideal_256": 128.0
    }

def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--message", type=str, help="ASCII/UTF-8 string")
    g.add_argument("--file", type=str, help="Path to bytes")
    ap.add_argument("--test-avalanche", action="store_true")
    ap.add_argument("--flips", type=int, default=16)
    args = ap.parse_args()

    if args.message is not None:
        data = args.message.encode("utf-8")
    else:
        with open(args.file, "rb") as f:
            data = f.read()

    if args.test_avalanche:
        rep = avalanche_test(data, flips=args.flips)
        print(json.dumps(rep, indent=2))
    else:
        h = arith_hash(data)
        print(json.dumps({
            "mode": "arith_hash",
            "len_bytes": len(data),
            "hash_hex": h
        }, indent=2))

if __name__ == "__main__":
    main()
