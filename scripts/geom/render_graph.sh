#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
DOT="${1:-analysis/geom/proof.dot}"
[ -s "$DOT" ] || { echo "[render] missing $DOT"; exit 2; }
if command -v dot >/dev/null 2>&1; then
  dot -Tpng "$DOT" -O && echo "[render] wrote ${DOT}.png"
else
  echo "[render] graphviz not found; install graphviz to render PNG."
fi
