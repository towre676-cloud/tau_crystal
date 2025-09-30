#!/usr/bin/env bash
set -u
PYBIN=""
for p in python3 python; do command -v "$p" >/dev/null 2>&1 && PYBIN="$p" && break; done
[ -z "$PYBIN" ] && { echo "[err] no Python"; exit 127; }
export PYTHONPATH=.
export FREED_SIGMA_MODE=${FREED_SIGMA_MODE:-mixed}
export FREED_TMF_MOCK=${FREED_TMF_MOCK:-1}
export FREED_TMF_EPS=${FREED_TMF_EPS:-1e-3}
export FREED_TMF_LEVELS=${FREED_TMF_LEVELS:-12,18,30}
export FREED_TMF_RTOL=${FREED_TMF_RTOL:-0.01}
export FREED_TMF_RTOL_PHI_ON=${FREED_TMF_RTOL_PHI_ON:-0.005}
export FREED_TMF_ATOL=${FREED_TMF_ATOL:-1e-6}
export FREED_APS_ETA=${FREED_APS_ETA:-1}
export FREED_W_STACK=${FREED_W_STACK:-B5}
export FREED_PHI_TWIST=${FREED_PHI_TWIST:-1}
export FREED_LOG_BASE=${FREED_LOG_BASE:-e}
"$PYBIN" scripts/freed/rg_leaf_checks.py || exit $?
"$PYBIN" scripts/freed/eta_tmf_report.py  || exit $?
"$PYBIN" scripts/freed/defect_functor.py  || exit $?
"$PYBIN" scripts/freed/axioms_table.py    || exit $?
echo "[ok] all receipts written. see analysis/freed + .tau_ledger/freed"
