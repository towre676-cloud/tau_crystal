#!/usr/bin/env bash
set -euo pipefail; set +H
LED="analysis/ramanujan/FROZEN_ETA.txt"
if [ $# -lt 3 ]; then echo "usage: $0 <id> <sturmBound> <witness_path> [expression...]"; exit 2; fi
id="$1"; sb="$2"; shift 2; wp="$1"; shift 1; expr="${*:-η(τ)^?}"
[ -f "$wp" ] || { echo "witness not found: $wp"; exit 3; }
hash=$(sha256sum "$wp" | awk "{print \$1}")
tmp=$(mktemp) ; touch "$LED";
awk -F"\\|" -v id="$id" '$0 ~ /^[[:space:]]*#/ {print; next} {gsub(/^[[:space:]]+|[[:space:]]+$/, "", $1); if($1==id) next; print}' "$LED" > "$tmp"
printf "%s\n" "# index | expression | SturmBound | witness SHA-256" > "$LED"
cat "$tmp" | awk '$0 ~ /^[[:space:]]*#/ {next} NF>0 {print}' >> "$LED"
printf "%s\n" "$id | ${expr} | ${sb} | sha256:${hash}" >> "$LED"
rm -f "$tmp"
echo "froze id=$id sb=$sb sha256:$hash (expr: $expr)"
