#!/usr/bin/env python3
import csv, sys, math, cmath
path = sys.argv[1] if len(sys.argv) > 1 else "tmp/ring.csv"
r    = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
M    = int(sys.argv[3]) if len(sys.argv) > 3 else 64
def f(z: complex) -> complex: return z  # replace with your model
with open(path, "a", newline="", encoding="utf-8") as fh:
    w = csv.writer(fh)
    for k in range(M):
        th = 2.0 * math.pi * k / M
        z = f(r * cmath.exp(1j * th))
        w.writerow([r, th, z.real, z.imag])
print(f"[ring] wrote r={r} with {M} samples → {path}")
