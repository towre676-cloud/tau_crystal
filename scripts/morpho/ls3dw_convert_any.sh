#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
SRC="${1:-}"; OUT="analysis/morpho/ref/datasets/ls3d_landmarks.tsv"
[ -n "$SRC" ] && [ -d "$SRC" ] || { echo "usage: $0 /path/to/LS3D-W"; exit 2; }
mkdir -p "$(dirname "$OUT")"
python3 scripts/morpho/ls3dw_mat_to_tsv.py "$SRC" "$OUT"
echo "→ $OUT"
