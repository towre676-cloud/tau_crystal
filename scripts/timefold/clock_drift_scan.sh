#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C

mapfile -t J < <(ls -1 .tau_ledger/ci/signed_runner/*_sig.json 2>/dev/null | LC_ALL=C sort)
[ "${#J[@]}" -ge 2 ] || { echo "[err] need >=2 signed_runner receipts"; exit 2; }

# extract ISO ts; compute deltas in seconds via GNU date or fallback
tsarr=()
for f in "${J[@]}"; do
  ts=$(sed -n 's/.*"ts":"\([^"]*\)".*/\1/p' "$f" | head -n1)
  [ -n "$ts" ] || continue
  tsarr+=("$ts")
done

secs() { date -u -d "$1" +%s 2>/dev/null || busybox date -u -D '%Y-%m-%dT%H:%M:%SZ' -d "$1" +%s 2>/dev/null || echo 0; }

anoms=0
minok=10     # min expected spacing in seconds (tweak)
maxok=$((48*3600))  # max spacing before we call it a gap (48h)

deltas=()
prev=""
for t in "${tsarr[@]}"; do
  if [ -n "$prev" ]; then
    a=$(secs "$prev"); b=$(secs "$t"); d=$(( b-a ))
    deltas+=("$d")
    if [ "$d" -lt "$minok" ] || [ "$d" -gt "$maxok" ]; then anoms=$((anoms+1)); fi
    if [ "$d" -lt 0 ]; then anoms=$((anoms+1)); fi
  fi
  prev="$t"
done

# summarize
cnt=${#deltas[@]}
sum=0; for d in "${deltas[@]}"; do sum=$((sum+d)); done
avg=$(awk -v s="$sum" -v n="$cnt" 'BEGIN{ if(n>0) printf("%.2f", s/n); else print "0.00" }')

tsnow="$(date -u +%FT%TZ)"
out=".tau_ledger/timefold/${tsnow//:/-}_clock_drift.json"
: > "$out"
printf '%s' "{" >> "$out"
printf '%s' "\"ts\":\"$tsnow\",\"samples\":$cnt,\"avg_gap_sec\":$avg,\"anomalies\":$anoms}" >> "$out"
echo "[ok] clock drift scan → $out (avg=${avg}s; anomalies=$anoms)"
