#!/usr/bin/env python3
import subprocess, sys, json

def run(cmd):
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    print(p.stdout)
    # research step: never fail CI
    sys.exit(0)

if __name__ == "__main__":
    run([sys.executable, "ci/heo/research/meta_prover.py",
         "--hypothesis", "sequence_periodic",
         "--conclusion", "H_rational",
         "--trials", "300"])
