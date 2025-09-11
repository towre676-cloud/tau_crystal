#!/usr/bin/env bash
set -Eeuo pipefail; set +H
src=".tau_ledger/bench/runs.ndjson"; out="docs/benchmarks/ci_speed.md"
mkdir -p "$(dirname "$out")"
[ -s "$src" ] || { printf "%s\n\n" "# CI speed benchmarks (receipt-backed)" > "$out"; echo "No runs yet." >> "$out"; exit 0; }
{
  echo "# CI speed benchmarks (receipt-backed)"
  echo
  echo "All entries are medians over attested runs from \`.tau_ledger/bench/runs.ndjson\`. The acceleration factor is cold/warm. Conditions: unchanged mathlib revision; same commit; identical runner image."
  echo
  echo "| OS | Runner | N(cold) | median_cold_s | N(warm) | median_warm_s | factor (cold/warm) |"
  echo "|---|---|---:|---:|---:|---:|---:|"
} > "$out"
keys_file=".tau_ledger/bench/.keys.$$"; awk 'match($0,/"os":"([^"]+)".*"runner":"([^"]+)"/,a){print a[1]"|"a[2]}' "$src" | sort -u > "$keys_file"
get_vals(){ awk -v os="$1" -v ru="$2" -v mo="$3" 'match($0,/"os":"([^"]+)".*"mode":"([^"]+)".*"runner":"([^"]+)".*"duration_s":([0-9]+)/,a){ if(a[1]==os && a[2]==mo && a[3]==ru) print a[4] }' "$src" | tr -d "\r" | sort -n; }
while IFS= read -r key; do [ -n "$key" ] || continue; os="${key%%|*}"; runner="${key#*|}";
  cold=$(get_vals "$os" "$runner" cold)
  warm=$(get_vals "$os" "$runner" warm)
  nc=$(printf "%s\n" "$cold" | awk "NF" | wc -l | tr -d " ")
  nw=$(printf "%s\n" "$warm" | awk "NF" | wc -l | tr -d " ")
  mc=$(printf "%s\n" "$cold" | awk '{x[NR]=$1} END{if(NR==0) print "NA"; else if(NR%2) print x[(NR+1)/2]; else {m=int(NR/2); printf "%.0f\n",(x[m]+x[m+1])/2}}')
  mw=$(printf "%s\n" "$warm" | awk '{x[NR]=$1} END{if(NR==0) print "NA"; else if(NR%2) print x[(NR+1)/2]; else {m=int(NR/2); printf "%.0f\n",(x[m]+x[m+1])/2}}')
  if [ "$mc" = "NA" ] || [ "$mw" = "NA" ] || [ "$mw" = "0" ]; then r="NA"; else r=$(awk -v c="$mc" -v w="$mw" 'BEGIN{printf "%.2f", c/w}'); fi
  printf "| %s | %s | %s | %s | %s | %s | %s |\n" "$os" "$runner" "$nc" "$mc" "$nw" "$mw" "$r" >> "$out"
done < "$keys_file"; rm -f "$keys_file"
