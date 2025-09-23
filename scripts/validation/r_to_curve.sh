#!/usr/bin/env bash
set -euo pipefail; set +H; . scripts/validation/_util.sh
IN="$1"; OUT="$2"; mkdir -p "$(dirname "$OUT")"
S=$(tr -d "\n\t " < "$IN")
A0=$(hash_to_z "$S:A" 2000001); A=$((A0-1000000))
B0=$(hash_to_z "$S:B" 2000001); B=$((B0-1000000))
disc_zero(){ local A=$1 B=$2; local t=$((4*A*A*A + 27*B*B)); [ $t -eq 0 ]; }
tries=0; while disc_zero "$A" "$B"; do A=$((A+1)); tries=$((tries+1)); [ $tries -gt 10 ] && { B=$((B+1)); tries=0; }; done
printf "%s\n" "A	$A" "B	$B" > "$OUT"
