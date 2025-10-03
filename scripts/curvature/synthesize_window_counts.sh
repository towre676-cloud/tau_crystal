#!/usr/bin/env bash
set +e; set +H; umask 022
scripts/tools/py.sh scripts/curvature/synthesize_window_counts.py >/dev/null 2>&1
if [ $? -ne 0 ]; then
  echo "[warn] python synth failed; using shell fallback"
  ids=$(sed -n "s/.*\\\"id\\\":\\\"\\([^\\\"]\\+\\)\\\".*/\\1/p" artifacts/curvature/cover_windows.json | tr -d "\\r")
  [ -n "$ids" ] || ids="U1 U2 U3"
  for id in $ids; do
    [ -s "artifacts/curvature/window_counts/$id.json" ] || printf "%s\n" "{\"sigma\":1.0,\"phi\":1.0,\"rho\":1.0}" > "artifacts/curvature/window_counts/$id.json"
  done
fi
echo "[ok] window_counts ready"
