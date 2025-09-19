#!/usr/bin/env python3
import sys, json, math, hashlib, struct, argparse

def tau2(k1,k2,th1,th2):
    # τ = det(I + M), with M_ij = sqrt(k_i k_j)/(k_i + k_j) * exp((θ_i+θ_j)/2)
    e1 = math.exp(th1/2.0)
    e2 = math.exp(th2/2.0)
    a11 = 0.5*e1*e1                    # k1/(2k1)*e^{θ1} = 0.5 e^{θ1}
    a22 = 0.5*e2*e2
    a12 = (math.sqrt(k1*k2)/(k1+k2))*e1*e2
    # det(I+M) for 2x2: (1+a11)(1+a22) - a12^2
    return (1.0+a11)*(1.0+a22) - a12*a12

def render_pgm(path, arr, w, h):
    # normalize to 0..255 by max value (avoid div0)
    vmax = max(arr) if arr else 1.0
    vscale = 255.0/(vmax if vmax>0 else 1.0)
    with open(path, "wb") as f:
        header = f"P5\n{w} {h}\n255\n".encode("ascii")
        f.write(header)
        for v in arr:
            x = int(v*vscale + 0.5)
            if x<0: x=0
            if x>255: x=255
            f.write(bytes([x]))

def main():
    ap = argparse.ArgumentParser(description="Deterministic 2-soliton τ/tanh demo for KdV: u = 2 ∂_x^2 log τ")
    ap.add_argument("--k1", type=float, default=1.0)
    ap.add_argument("--k2", type=float, default=0.7)
    ap.add_argument("--d1", type=float, default=-4.0, help="delta1")
    ap.add_argument("--d2", type=float, default=+3.0,  help="delta2")
    ap.add_argument("--n", type=int, default=2048)
    ap.add_argument("--xmin", type=float, default=-20.0)
    ap.add_argument("--xmax", type=float, default=20.0)
    ap.add_argument("--expect", type=str, default="")
    ap.add_argument("--out", type=str, default="")
    ap.add_argument("--pgm", type=str, default="")
    ap.add_argument("--scale", type=float, default=1e12, help="fixed-point scale for hashing")
    args = ap.parse_args()

    n = int(args.n)
    if n<5 or not math.isfinite(args.xmin) or not math.isfinite(args.xmax) or args.xmax<=args.xmin:
        print("[err] bad grid", file=sys.stderr); sys.exit(2)

    k1,k2 = float(args.k1), float(args.k2)
    d1,d2 = float(args.d1), float(args.d2)
    xmin,xmax = float(args.xmin), float(args.xmax)
    dx = (xmax - xmin)/(n-1)

    # compute ln τ on grid, then u = 2 * (lnτ(x+h) - 2 lnτ(x) + lnτ(x-h))/h^2
    ln_tau = [0.0]*n
    for i in range(n):
        x = xmin + i*dx
        th1 = k1*x + d1           # t = 0
        th2 = k2*x + d2
        tau = tau2(k1,k2,th1,th2)
        if tau <= 0.0 or not math.isfinite(tau):
            # extremely unlikely in this setup; clamp to tiny positive to keep determinism
            tau = 1e-300
        ln_tau[i] = math.log(tau)

    u = [0.0]*n
    inv_dx2 = 1.0/(dx*dx)
    # central differences for interior; simple one-sided at ends
    u[0]      = 2.0 * (ln_tau[1] - ln_tau[0]) * inv_dx2    # crude, deterministic
    u[n-1]    = 2.0 * (ln_tau[n-1] - ln_tau[n-2]) * inv_dx2
    for i in range(1,n-1):
        u[i] = 2.0 * (ln_tau[i+1] - 2.0*ln_tau[i] + ln_tau[i-1]) * inv_dx2

    # deterministic fixed-point hashing
    scale = float(args.scale)
    h = hashlib.sha256()
    u_max = 0.0
    sum_u2 = 0.0
    for val in u:
        if not math.isfinite(val): val = 0.0
        if val>u_max: u_max = val
        sum_u2 += val*val
        q = int(round(val*scale))
        if q >  0x7fffffffffffffff: q =  0x7fffffffffffffff
        if q < -0x8000000000000000: q = -0x8000000000000000
        h.update(struct.pack('<q', q))
    sha = h.hexdigest()
    l2 = math.sqrt(sum_u2*dx)

    out = {
        "algo": "2-soliton: tau=det(I+M), M_ij=sqrt(k_i k_j)/(k_i+k_j)*exp((θ_i+θ_j)/2); u=2*∂_x^2 log tau via central differencing",
        "k1":k1,"k2":k2,"d1":d1,"d2":d2,
        "grid":{"n":n,"xmin":xmin,"xmax":xmax,"dx":dx},
        "scale":scale,"sha256":sha,
        "u_max": float(f"{u_max:.12e}"),
        "l2": float(f"{l2:.12e}")
    }
    js = json.dumps(out, sort_keys=True, separators=(",",":"))
    if args.out:
        with open(args.out,"w",encoding="utf-8") as f: f.write(js+"\n")
    print(js)

    if args.pgm:
        # simple 1-D image: height=1; duplicate to 128 rows for nicer preview
        tmp_row = u
        hgt = 128
        img = tmp_row * hgt
        render_pgm(args.pgm, img, len(tmp_row), hgt)

    if args.expect and sha.lower()!=args.expect.lower():
        print(f"[DRIFT] expected {args.expect} != got {sha}", file=sys.stderr)
        sys.exit(1)
    sys.exit(0)

if __name__=="__main__":
    main()
