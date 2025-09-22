#!/usr/bin/env bash
set -euo pipefail
src="${1:-_ci_artifacts}"
dst="docs/gallery"
mkdir -p "$dst"
list=(tau_tanh_demo.png interference.svg qr-witness.svg)
for f in "${list[@]}"; do
  if [ -f "$src/$f" ]; then
    cp -f "$src/$f" "$dst/$f"
    echo "[gallery] copied $src/$f -> $dst/$f"
  else
    echo "[gallery] missing $src/$f (skipped)"
  fi
done
