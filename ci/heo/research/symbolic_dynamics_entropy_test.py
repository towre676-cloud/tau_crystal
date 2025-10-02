#!/usr/bin/env python3
import sys, subprocess, json
p = subprocess.run([sys.executable, "ci/heo/research/symbolic_dynamics_entropy.py",
                    "--sequence", "ci/data/sequences/periodic_7_0010010.json",
                    "--max-block-length", "14"],
                   text=True, capture_output=True)
print(p.stdout)
sys.exit(0)
