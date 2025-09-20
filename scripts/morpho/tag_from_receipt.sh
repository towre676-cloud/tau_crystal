#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
PACK="${1:-}"
[ -n "$PACK" ] && [ -d "$PACK" ] || { echo "usage: $0 PACK_DIR" >&2; exit 2; }
REC="$PACK/corridor.receipt.tsv"
[ -f "$REC" ] || { echo "missing $REC" >&2; exit 3; }
ROOT="$(awk '$1=="ROOT"{print $2}' "$REC" | head -n1)"
[ -n "$ROOT" ] || { echo "no ROOT in receipt" >&2; exit 4; }
TAG="morpho-pack-${ROOT:0:12}"
git tag -f "$TAG"
git push origin "refs/tags/$TAG" -f
echo "retagged: $TAG"
