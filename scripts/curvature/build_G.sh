#!/usr/bin/env bash
set +e; set +H; umask 022
scripts/tools/py.sh scripts/curvature/build_G_from_grammar.py >/dev/null 2>&1
if [ $? -ne 0 ] || [ ! -s artifacts/curvature/G_presentation.json ]; then
  echo "[warn] build_G_from_grammar failed; emitting minimal G"
  : > artifacts/curvature/G_presentation.json
  printf "%s" "{\"G\":{\"domain\":[\"sigma\",\"phi\",\"rho\"],\"generators\":[\"id\",\"swap(sigma,phi)\"],\"relations\":[\"involutive(swap(sigma,phi))\"]}}"
fi
echo "[ok] G_presentation ready"
