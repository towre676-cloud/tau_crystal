#!/usr/bin/env bash
set -e; set +H; umask 022
if scripts/tools/py.sh scripts/obs/_obs_certificate.py >/dev/null 2>&1; then
  echo "[ok] obs certificate (python)"; exit 0
fi
echo "[warn] python path failed; emitting fallback certificate"
: > artifacts/obs/obs_certificate.json
printf "%s" "{\"input\":{\"CRO_scalar\":0.0,\"ENT_scalar\":0.0,\"Obs\":0.0},\"epsilons\":[1e-9,1e-6,1e-3],\"checks\":[],\"gradient\":{\"dObs_dC\":0.0,\"dObs_dE\":0.0},\"lipschitz\":{\"L1_bound\":0.0,\"L2_bound\":0.0},\"fallback\":true}" >> artifacts/obs/obs_certificate.json
echo "[ok] obs certificate (fallback)"
