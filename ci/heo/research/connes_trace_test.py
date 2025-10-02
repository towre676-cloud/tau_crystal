#!/usr/bin/env python3
import sys, subprocess
p = subprocess.run([sys.executable, "ci/heo/research/connes_trace_formula.py",
                    "--sequence", "ci/data/sequences/periodic_7_0010010.json",
                    "--K", "150000", "--tolerance", "0.05"],
                   text=True, capture_output=True)
print(p.stdout)
# Non-blocking research check
sys.exit(0)
