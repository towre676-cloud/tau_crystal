#!/usr/bin/env bash
set -euo pipefail; set +H
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
TAB="${1:-ramanujan/data/tau_small.tsv}"
LIMIT="${2:-2000}"
FILE="$ROOT/$TAB"
[ -f "$FILE" ] || { echo "missing $TAB"; exit 3; }
declare -A T
while IFS=$'\t' read -r n v; do [[ -z "${n:-}" ]] && continue; T[$n]="$v"; done < "$FILE"
ok=1
for ((m=1; m<=LIMIT; m++)); do
  for ((n=1; n<=LIMIT; n++)); do
    prod=$((m*n)); if (( prod>LIMIT )); then break; fi
    # coprime check
    a=$m; b=$n; while (( b != 0 )); do tmp=$((a%b)); a=$b; b=$tmp; done; g=$a
    if (( g==1 )) && [[ -n "${T[$m]:-}" && -n "${T[$n]:-}" && -n "${T[$prod]:-}" ]]; then
      expect=$(( T[$m] * T[$n] ))
      if [ "${T[$prod]}" != "$expect" ]; then echo "BAD\t$m\t$n"; ok=0; break; fi
    fi
  done
  (( ok==1 )) || break
done
if (( ok==1 )); then echo "OK\tHecke multiplicativity up to $LIMIT";
  REC="$ROOT/ramanujan/receipts/tau_hecke_$(date -u +%Y%m%dT%H%M%SZ).tsv"
  printf "%s\n" "time\t$(date -u +%FT%TZ)" "table\t$TAB" "limit\t$LIMIT" "status\tOK" > "$REC"
  echo "$REC"
  exit 0
else exit 1; fi
