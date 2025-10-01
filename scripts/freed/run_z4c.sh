#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
python3 - <<'PY'
import os, glob, time, json, subprocess, sys
def run(test, res, glued):
    out = subprocess.check_output([
      sys.executable,"scripts/freed/z4c_nonlinear_1d.py",
      "--test",test,"--res",str(res),"--glued",str(glued),"--T","1.0"
    ], text=True).strip()
    print(f"[z4c] {test} N={res} glued={glued} -> {out}")
for test in ("gauge","robust"):
  for res in (801,1201):
    for glued in (0,1):
      run(test,res,glued)
PY
