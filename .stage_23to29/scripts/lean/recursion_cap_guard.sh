#!/usr/bin/env bash
set +H; umask 022
cap_file="${1:-.tau_ledger/phys/debye_cap.txt}"
src_dir="${2:-.}"
HARD="${HARD:-0}"
[ -f "$cap_file" ] || { echo "[err] missing cap: $cap_file"; [ "$HARD" = "1" ] && exit 2 || exit 0; }
cap=$(tr -d "\r\n " < "$cap_file")
case "$cap" in (*[!0-9]*) echo "[err] bad cap: $cap"; [ "$HARD" = "1" ] && exit 3 || exit 0;; esac
cnt=$(find "$src_dir" -type f -name "*.lean" -print0 2>/dev/null | xargs -0 grep -l "^\s*mutual" 2>/dev/null | wc -l | tr -d " \t")
echo "mutual_blocks=$cnt cap=$cap"
if [ "$cnt" -le "$cap" ]; then exit 0; fi
echo "::error ::mutual recursion blocks exceed Debye cap"
[ "$HARD" = "1" ] && exit 4 || exit 0
