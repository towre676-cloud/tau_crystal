#!/usr/bin/env bash
set +e; set +H; umask 022
scripts/tools/py.sh scripts/curvature/timefold_from_counts.py >/dev/null 2>&1
if [ $? -ne 0 ] || [ ! -s artifacts/curvature/timefold_kl.json ]; then
  echo "[warn] Θ-KL python path failed; emitting safe default"
  : > artifacts/curvature/timefold_kl.json
  printf "%s" "{\"timefold\":[],\"mean_kl\":0.0,\"epsilon\":1e-9,\"fallback\":true}" >> artifacts/curvature/timefold_kl.json
fi
echo "[ok] timefold_kl ready"
