#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
PACK="${1:-}"
[ -n "$PACK" ] && [ -d "$PACK" ] || { echo "usage: $0 PACK_DIR" >&2; exit 2; }
REC="$PACK/corridor.receipt.tsv"; GLB="$PACK/global.L"
[ -f "$REC" ] && [ -f "$GLB" ] || { echo "missing receipt/global.L" >&2; exit 3; }
H="$(awk -F= '/^H_BAR=/{print $2}' "$GLB" | head -n1)"
ROOT="$(awk '$1=="ROOT"{print $2}' "$REC" | head -n1)"
TS="$(awk -F= '/^PACK_TIMESTAMP=/{print $2}' "$REC" | head -n1)"
[ -n "$TS" ] || TS="$(date -u +"%Y-%m-%dT%H:%MZ")"
BASE="$(basename "$PACK")"
mkdir -p analysis/morpho
printf "%s\tH_BAR=%s\tROOT=%s\tPACK=%s\n" "$TS" "$H" "$ROOT" "$BASE" >> analysis/morpho/manifest.tsv
