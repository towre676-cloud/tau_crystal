#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
PACK="${1:-}"; FACE="${2:-}"
[ -d "$PACK" ] && [ -f "$PACK/corridor.receipt.tsv" ] && [ -f "$FACE" ] || { echo "usage: $0 PACK_DIR face.tsv" >&2; exit 2; }
REC="$PACK/corridor.receipt.tsv"
SCORES=$(scripts/morpho/ref_anchor.sh "$FACE") || exit 3
MAH=$(printf "%s\n" "$SCORES" | awk -F= '/MAHALANOBIS/{print $2}')
RS=$(printf "%s\n" "$SCORES" | awk -F= '/^REF_SIG/{print $2}')
grep -q "^REF_SIG" "$REC" || printf "REF_SIG\t%s\n" "$RS" >> "$REC"
grep -q "^MAHALANOBIS" "$REC" || printf "MAHALANOBIS\t%s\n" "$MAH" >> "$REC"
echo "stamped REF_SIG=$RS MAHALANOBIS=$MAH → $REC"
