#!/usr/bin/env python3
import json, argparse, sys

def load_sequence(path):
    with open(path, "r") as f:
        obj = json.load(f)
    kind = obj.get("kind")
    if kind == "periodic":
        patt = obj["pattern"]
        return lambda n: patt[(n-1) % len(patt)]
    elif kind == "explicit":
        values = obj["values"]
        return lambda n: values[n-1] if 1 <= n <= len(values) else 0
    else:
        raise ValueError("unknown kind")

def limsup_density(X, Nmax=200000, window=5000):
    best = 0.0
    s = 0
    for n in range(1, Nmax+1):
        s += X(n)
        if n % window == 0:
            best = max(best, s/n)
    return best, s/Nmax

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence", required=True)
    ap.add_argument("--d", required=True)
    ap.add_argument("--k", required=True)
    ap.add_argument("--assert-bounds", nargs=2, type=float)
    ap.add_argument("--assert-limsup-le", type=float)
    args = ap.parse_args()

    X = load_sequence(args.sequence)
    ls, last = limsup_density(X)
    print(json.dumps({"limsup": ls, "last": last}, indent=2))

    if args.assert_bounds:
        lo, hi = args.assert_bounds
        assert 0.0 - 1e-12 <= ls <= 1.0 + 1e-12
        assert lo - 1e-12 <= ls <= hi + 1e-12
    if args.assert_limsup_le is not None:
        assert ls <= args.assert_limsup_le + 1e-12

if __name__ == "__main__":
    main()
