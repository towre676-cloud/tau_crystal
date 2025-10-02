#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
MARK="${1:-}"; [ -n "$MARK" ] || { echo "[err] usage: timefold_replay.sh PATH/mark.json"; exit 64; }
CJSON="$(tr -d "\r\n" < "$MARK")"
CREF="$(printf "%s" "$CJSON" | sed -n 's/.*"corridor_receipt":"\([^"]*\)".*/\1/p')"
CSHA="$(printf "%s" "$CJSON" | sed -n 's/.*"corridor_sha":"\([^"]*\)".*/\1/p')"
echo "[info] corridor_receipt: ${CREF:-<empty>}"
echo "[info] corridor_sha:     ${CSHA:-<empty>}"
[ -n "${CREF:-}" ] || { echo "[err] mark missing corridor_receipt"; exit 66; }
[ -f "$CREF" ] || { echo "[err] corridor receipt not found: $CREF"; exit 66; }
echo "[replay] would restore state corresponding to $CREF"
exit 0
