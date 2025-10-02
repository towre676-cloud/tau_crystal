#!/usr/bin/env bash
set -euo pipefail; set +H
WORK="${1:-validation/work}"
OUT="${2:-analysis/validation/ap_tau_by_face.csv}"
mkdir -p "$(dirname "$OUT")"
primes="$(mktemp)"; rows="$(mktemp)"
for d in "$WORK"/face*/; do [ -d "$d" ] || continue; f="$d/a_p.tsv"; [ -s "$f" ] || continue; awk "{print \$1}" "$f" >> "$primes"; done
if [ ! -s "$primes" ]; then printf "%s\n" "2\n3\n5\n7\n11\n13\n17\n19\n23\n29\n31\n37" > "$primes"; fi
PR=($(sort -n "$primes" | awk '!seen[$0]++'))
printf "face" > "$OUT"; for p in "${PR[@]}"; do printf ",%s" "$p" >> "$OUT"; done; printf "\n" >> "$OUT"
for d in "$WORK"/face*/; do [ -d "$d" ] || continue; face="$(basename "$d")"; f="$d/a_p.tsv"; declare -A M=(); if [ -s "$f" ]; then while read -r p ap; do M["$p"]="$ap"; done < "$f"; fi; printf "%s" "$face" >> "$OUT"; for p in "${PR[@]}"; do printf ",%s" "${M[$p]:-}" >> "$OUT"; done; printf "\n" >> "$OUT"; unset M; done
