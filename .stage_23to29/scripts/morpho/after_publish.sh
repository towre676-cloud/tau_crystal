#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
PACK_DIR="${PACK_DIR:-${1:-}}"
[ -n "$PACK_DIR" ] && [ -d "$PACK_DIR" ] || { echo "after_publish: PACK_DIR unset or missing" >&2; exit 2; }
scripts/morpho/stamp_hbar_root.sh "$PACK_DIR" || exit 3
H="$(awk -F= '/^H_BAR=/{print $2}' "$PACK_DIR/global.L" | head -n1)"
ROOT="$(awk '$1=="ROOT"{print $2}' "$PACK_DIR/corridor.receipt.tsv" | head -n1)"
COUNT="$(find "$PACK_DIR" -maxdepth 1 -type f | wc -l | awk "{print \$1}")"
echo "published: $PACK_DIR  (H_BAR=$H, files=$COUNT, root=$ROOT)"
