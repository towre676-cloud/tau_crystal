#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C

base="${1:-}"; curr="${2:-}"
[ -n "$base" ] || base="$(ls -1 .tau_ledger/interference/*_summary.json 2>/dev/null | head -n 1 || true)"
[ -n "$curr" ] || curr="$(ls -1 .tau_ledger/interference/*_summary.json 2>/dev/null | tail -n 1 || true)"
[ -s "$base" ] && [ -s "$curr" ] || { echo "[err] need baseline and current summaries"; exit 2; }

val(){ sed -n "s/.*\"$1\":\(\"[^\"]*\"\\|[-0-9.]*\\).*/\\1/p" "$2" | head -n1 | sed 's/^"//;s/"$//' ; }

b_ts=$(val ts "$base"); b_lag=$(val best_lag "$base"); b_score=$(val best_score "$base")
c_ts=$(val ts "$curr"); c_lag=$(val best_lag "$curr"); c_score=$(val best_score "$curr")

[ -n "$b_lag" ] && [ -n "$c_lag" ] || { echo "[err] could not parse lag/score"; exit 3; }

dlag=$(( c_lag - b_lag ))
# score delta via awk to preserve floating point
dscore=$(awk -v a="$c_score" -v b="$b_score" 'BEGIN{printf("%.6f", a-b)}')

ts="$(date -u +%FT%TZ)"
out=".tau_ledger/interference/${ts//:/-}_drift.json"
: > "$out"
printf '%s' "{" >> "$out"
printf '%s' "\"ts\":\"$ts\"," >> "$out"
printf '%s' "\"baseline\":\"$(printf '%s' "$base" | sed 's/\"/'\''/g')\"," >> "$out"
printf '%s' "\"current\":\"$(printf '%s' "$curr" | sed 's/\"/'\''/g')\"," >> "$out"
printf '%s' "\"delta\":{\"lag\":$dlag,\"score\":$dscore}}" >> "$out"
echo "[ok] drift → $out (Δlag=$dlag, Δscore=$dscore)"
