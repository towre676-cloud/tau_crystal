#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
BASE=".tau_ledger/lean_module_capsules"; OUT="docs/ledger/descent_chains.json"; : > "$OUT"
printf "[" >> "$OUT"; sep=""
find "$BASE" -type f -name "*.json" ! -name "index.json" ! -name "capsule_set.seal.json" -print0 | sort -z | while IFS= read -r -d "" j; do
  mod=$(grep -m1 "\"module\":" "$j" | sed -E "s/.*\"module\":\"([^\"]+)\".*/\\1/")
  [ -n "$mod" ] || continue
  # imports array → flat list
  mapfile -t imps < <(grep -o "\"imports\":[[][^]]*[]]" "$j" | sed -E "s/.*\\[\\s*(.*)\\s*\\].*/\\1/" | tr "," "\n" | sed -E "s/[\"\\s]//g" | sed "/^$/d")
  printf "%s{" "$sep" >> "$OUT"; sep=","
  printf "\"module\":\"%s\",\"imports\":" "$mod" >> "$OUT"
  if [ ${#imps[@]} -eq 0 ]; then printf "[]" >> "$OUT"; else printf "[" >> "$OUT"; s2=""; for x in "${imps[@]}"; do printf "%s\"%s\"" "$s2" "$x" >> "$OUT"; s2=","; done; printf "]" >> "$OUT"; fi
  printf "}" >> "$OUT"
done
printf "]\n" >> "$OUT"
