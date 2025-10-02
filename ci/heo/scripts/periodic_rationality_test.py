#!/usr/bin/env python3
import json, argparse, fractions

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sequence", required=True)
    args = ap.parse_args()
    obj = json.load(open(args.sequence))
    patt = obj["pattern"]
    T = len(patt)
    q = sum(patt) / T
    rat = fractions.Fraction(sum(patt), T)
    print(json.dumps({"period": T, "sum": sum(patt), "ratio": float(rat), "rational": f"{rat.numerator}/{rat.denominator}"}))
    assert abs(q - float(rat)) < 1e-12

if __name__ == "__main__":
    main()
