#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
MODE="${1:-soft}"   # soft|hard
PACK="${2:-}"
[ -n "$PACK" ] && [ -d "$PACK" ] || { echo "geom_gate: usage: $0 soft|hard PACK_DIR" >&2; exit 2; }
LOG="$PACK/geom_strict.log"
OUT="$PACK/geom_strict.out"
ERR="$PACK/geom_strict.err"
: > "$LOG"; : > "$OUT"; : > "$ERR"
echo "== geom strict gate on $PACK ==" >> "$LOG"
# Replace the next line with your actual strict validator command if different:
scripts/morpho/strict_validate.sh "$PACK" >"$OUT" 2>"$ERR" || VALID_EXIT=$?
VALID_EXIT=${VALID_EXIT:-0}
if [ "$VALID_EXIT" -eq 0 ]; then
  echo "strict: PASS" | tee -a "$LOG"
  exit 0
fi
echo "strict: FAIL (exit=$VALID_EXIT)" | tee -a "$LOG"
if [ -s "$OUT" ]; then tail -n 20 "$OUT" | sed "s/^/[out] /" | tee -a "$LOG"; fi
if [ -s "$ERR" ]; then tail -n 20 "$ERR" | sed "s/^/[err] /" | tee -a "$LOG"; fi
case "$MODE" in
  soft) echo "strict: SOFT gate — continuing" | tee -a "$LOG"; exit 0 ;;
  hard) echo "strict: HARD gate — blocking release" | tee -a "$LOG"; exit "$VALID_EXIT" ;;
  *)    echo "geom_gate: unknown mode: $MODE" >&2; exit 3 ;;
esac
