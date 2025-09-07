#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
exec </dev/null

ROOT="${1:-$PWD}"
cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }

LOGDIR=".tau_ledger/debug"; mkdir -p "$LOGDIR"
TS="$(date -u +%Y%m%dT%H%M%SZ)"
LOG="$LOGDIR/diag-$TS.log"
: >"$LOG" || { echo "[err] cannot write $LOG"; exit 1; }

say(){ printf "%s\n" "$*" | tee -a "$LOG"; }

latest_log(){
  local best="" f
  for f in "$LOGDIR"/diag-*.log; do
    [ -e "$f" ] || continue
    case "$f" in *"/diag-"*"Z.log") : ;; *) continue ;; esac
    best="$f"
  done
  [ -n "${best:-}" ] && printf "%s\n" "$best" || true
}

say "[sys] uname:"
uname -a | tee -a "$LOG"

say ""
say "[sys] shell:"
printf "%s\n" "${SHELL:-unknown}" | tee -a "$LOG"

say ""
say "[diag] previous log tail (up to 200 lines):"
prev="$(latest_log || true)"
if [ -n "${prev:-}" ] && [ "$prev" != "$LOG" ]; then
  say "[diag] previous: $prev"
  tail -n 200 -- "$prev" | tee -a "$LOG"
else
  say "[diag] none"
fi

say ""
say "[diag] active processes (grep tau_crystal):"
ps -W 2>/dev/null | tr -d "\r" | grep -i "tau_crystal" && true || say "[diag] none"

say ""
say "[ok] wrote diagnostic snapshot to $LOG"
