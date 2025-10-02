#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
PACK="${1:-}"
[ -n "$PACK" ] && [ -d "$PACK" ] || { echo "usage: $0 PACK_DIR" >&2; exit 2; }
OUT="$PACK/pack_verify.out"; ERR="$PACK/pack_verify.err"
: > "$OUT"; : > "$ERR"
if [ -x scripts/morpho/pack_verify.sh ]; then
  scripts/morpho/pack_verify.sh "$PACK" >"$OUT" 2>"$ERR" || PV_EXIT=$?
else
  echo "strict_validate: missing scripts/morpho/pack_verify.sh" >&2; exit 127
fi
PV_EXIT=${PV_EXIT:-0}
if grep -q "^[[]strict[]] *FAIL" "$OUT" "$ERR" 2>/dev/null; then exit 1; fi
if grep -q "^judge: OK" "$OUT" 2>/dev/null; then exit 0; fi
exit "$PV_EXIT"
