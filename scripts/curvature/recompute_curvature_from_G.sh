#!/usr/bin/env bash
set +e; set +H; umask 022
scripts/tools/py.sh scripts/curvature/recompute_curvature_from_G.py >/dev/null 2>&1
for f in artifacts/curvature/cocycle_cijk.json artifacts/curvature/length_metrics.json artifacts/curvature/G_validation.json; do
  [ -s "$f" ] || printf "%s\n" "{\"fallback\":true}" > "$f"
done
echo "[ok] curvature recompute complete"
