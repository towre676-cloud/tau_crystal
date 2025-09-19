#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
in="$1"; out="${2:-analysis/morpho/input/landmarks_clean.csv}"
[ -f "$in" ] || { echo "missing landmarks"; exit 2; }
mkdir -p "$(dirname "$out")"
awk -v OFS=, '{
  line=$0; sub(/\r$/,"",line)
  if(index(line,",")==0) n=split(line,a,/[[:space:]]+/); else n=split(line,a,/,/)
  if(n<4) next
  ok=1; for(i=1;i<=4;i++){ gsub(/^[[:space:]]+|[[:space:]]+$/,"",a[i]); if(a[i]!~/^-?[0-9]+(\.[0-9]+)?$/) ok=0 }
  if(ok) print a[1],a[2],a[3],a[4]
}' "$in" > "$out"
[ -s "$out" ] || { echo "no valid numeric rows"; exit 3; }
echo "cleaned -> $out"

