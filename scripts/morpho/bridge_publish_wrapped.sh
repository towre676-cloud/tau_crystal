#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
scripts/morpho/bridge_and_publish.sh "$@" || true
PACK_DIR="${PACK_DIR:-${1:-}}"
[ -n "$PACK_DIR" ] && [ -d "$PACK_DIR" ] || PACK_DIR="$(scripts/morpho/latest_complete_pack.sh 2>/dev/null || true)"
[ -n "$PACK_DIR" ] && [ -d "$PACK_DIR" ] || { echo "wrap: no complete pack found"; exit 0; }
scripts/morpho/after_publish.sh "$PACK_DIR" || exit 4
