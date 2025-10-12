#!/usr/bin/env bash
set -euo pipefail
set +H
export LC_ALL=C
. "$(dirname "$0")/merkle_lib.sh"
if [ "$#" -ne 4 ]; then echo "usage: build_stack.sh GEO TORSION_LIST OUT_JSON OUT_ROOT" >&2; exit 64; fi
geo="$1"; tors="$2"; out_json="$3"; out_root="$4"
mkdir -p ".tau_ledger/stack/$geo"
sed -E "s/\r$//" "$tors" | grep -v "^[[:space:]]*$" | sort -u > ".tau_ledger/stack/$geo/_alphas.txt"
: > ".tau_ledger/stack/$geo/_leaves.txt"
while IFS= read -r alpha; do [ -z "$alpha" ] && continue; leaf="$(sha256_text "$alpha")"; printf "%s\n" "$leaf" >> ".tau_ledger/stack/$geo/_leaves.txt"; done < ".tau_ledger/stack/$geo/_alphas.txt"
root="$(merkle_root_from_file ".tau_ledger/stack/$geo/_leaves.txt")"
printf "%s\n" "$root" > "$out_root"
: > "$out_json"
printf "{" >> "$out_json"
printf "\"geometry\":{\"tag\":\"%s\"}" "$geo" >> "$out_json"
printf ",\"alphas\":[" >> "$out_json"
c=0; while IFS= read -r a; do [ -z "$a" ] && continue; if [ $c -gt 0 ]; then printf "," >> "$out_json"; fi; printf "\"%s\"" "$a" >> "$out_json"; c=$((c+1)); done < ".tau_ledger/stack/$geo/_alphas.txt"
printf "]" >> "$out_json"
printf ",\"leaves\":[" >> "$out_json"
c=0; while IFS= read -r h; do [ -z "$h" ] && continue; if [ $c -gt 0 ]; then printf "," >> "$out_json"; fi; printf "\"%s\"" "$h" >> "$out_json"; c=$((c+1)); done < ".tau_ledger/stack/$geo/_leaves.txt"
printf "]" >> "$out_json"
printf ",\"merkle_root\":\"%s\"}" "$root" >> "$out_json"
