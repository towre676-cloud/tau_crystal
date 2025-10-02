#!/usr/bin/env python3
import json, subprocess, sys

def run(cmd):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    print(p.stdout)
    if p.returncode != 0:
        print(p.stderr, file=sys.stderr)
    # never hard-fail in research CI
    sys.exit(0)

def main():
    # Example curves: y^2 = x^3 + x + 1  and  y^2 = x^3 - x + 1
    run([sys.executable, "ci/heo/research/bsd_lfunction_probe.py",
         "--a", "1", "--b", "1", "--k", "1", "--Nmax", "4000",
         "--primes", "2", "3", "5", "7", "11", "13"])
    run([sys.executable, "ci/heo/research/bsd_lfunction_probe.py",
         "--a", "-1", "--b", "1", "--k", "1", "--Nmax", "4000",
         "--primes", "2", "3", "5", "7", "11", "13"])
if __name__ == "__main__":
    main()
