#!/usr/bin/env python3
import sys, subprocess
p = subprocess.run([sys.executable, "ci/heo/research/heat_kernel_residue.py",
                    "--sequence", "ci/data/sequences/periodic_7_0010010.json",
                    "--tolerance", "0.05"],
                   text=True, capture_output=True)
print(p.stdout)
sys.exit(0)
