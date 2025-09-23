#!/usr/bin/env python3
import sys, json, math, hashlib, struct, argparse
def sech2(z: float) -> float:
    c = math.cosh(z)
    return 1.0/(c*c)
def main():
    ap = argparse.ArgumentParser(description="Deterministic one-soliton envelope: u = (k^2/2) * sech^2(theta/2), theta = k*x + delta (t=0)")
    ap.add_argument("--k", type=float, default=1.0)
    ap.add_argument("--delta", type=float, default=0.0)
    ap.add_argument("--n", type=int, default=2048)
    ap.add_argument("--xmin", type=float, default=-20.0)
    ap.add_argument("--xmax", type=float, default=20.0)
    ap.add_argument("--expect", type=str, default="")
    ap.add_argument("--out", type=str, default="")
    ap.add_argument("--scale", type=float, default=1e12, help="fixed-point scale for hashing (default 1e12)")
    args = ap.parse_args()

    if args.n <= 1 or args.xmax <= args.xmin:
        print("[err] bad grid", file=sys.stderr); sys.exit(2)

    # fixed grid and step
    n = int(args.n)
    xmin, xmax = float(args.xmin), float(args.xmax)
    dx = (xmax - xmin) / (n - 1)

    # deterministic fixed-point hashing to avoid libm drift
    k, delta = float(args.k), float(args.delta)
    scale = float(args.scale)
    h = hashlib.sha256()
    u_max = 0.0
    sum_u2 = 0.0

    for i in range(n):
        x = xmin + i*dx
        th = k*x + delta            # t = 0 for determinism
        u = 0.5*(k*k)*sech2(0.5*th) # envelope
        if not math.isfinite(u): u = 0.0
        u_max = u if u>u_max else u
        sum_u2 += u*u
        # fixed-point 64-bit signed int
        q = int(round(u*scale))
        if q >  0x7fffffffffffffff: q =  0x7fffffffffffffff
        if q < -0x8000000000000000: q = -0x8000000000000000
        h.update(struct.pack('<q', q))

    sha = h.hexdigest()
    # present summary with stable text formatting
    l2 = math.sqrt(sum_u2*dx)
    out = {
        "algo": "u=(k^2/2)*sech^2((k*x+delta)/2), t=0; hash over fixed-point q=round(u*scale)",
        "k": k, "delta": delta,
        "grid": {"n": n, "xmin": xmin, "xmax": xmax, "dx": dx},
        "scale": scale,
        "sha256": sha,
        "u_max": float(f"{u_max:.12e}"),
        "l2": float(f"{l2:.12e}")
    }

    js = json.dumps(out, sort_keys=True, separators=(",",":"))
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f: f.write(js+"\n")
    print(js)

    if args.expect:
        if sha.lower() != args.expect.lower():
            print(f"[DRIFT] expected {args.expect} != got {sha}", file=sys.stderr)
            sys.exit(1)
    sys.exit(0)

if __name__ == "__main__":
    main()
