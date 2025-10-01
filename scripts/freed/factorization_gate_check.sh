#!/usr/bin/env bash
set +e; umask 022; export LC_ALL=C LANG=C
TOL_ON="${TOL_ON:-1e-7}"; TOL_OFF="${TOL_OFF:-1e-10}"
for mode in on off; do
  p="$(ls -1 analysis/freed/*_factorization_phi_${mode}.json 2>/dev/null | tail -n1 || true)"
  if [ -z "$p" ]; then echo "[warn] no factorization file for phi=${mode}"; continue; fi
  res="$(python - <<'PY' "$p"
import json,sys
d=json.load(open(sys.argv[1],'r',encoding='utf-8'))
val=None
for k in ("residual","resid","error","delta"):
  if k in d and isinstance(d[k],(int,float)): val=float(d[k]); break
print("NaN" if val is None else val)
PY
)"
  echo "[phi=${mode}] residual=${res}"
done
