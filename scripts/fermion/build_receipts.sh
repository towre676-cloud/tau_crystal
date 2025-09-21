#!/usr/bin/env bash
set +H; set -euo pipefail; umask 022
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
LEDGER="analysis/fermion/ledger.tsv"
OUT="analysis/fermion/fermion.receipt.json"
STAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
COIN=$(printf "%s" "$(sha256sum analysis/fermion/ledger.tsv | awk "{print \$1}")")
rm -f "$OUT"; printf "{" >> "$OUT"
printf "\"built\":\"%s\",\"coin\":\"%s\",\"entries\":[" "$STAMP" "$COIN" >> "$OUT"
first=1
tail -n +2 "$LEDGER" | while IFS=$'\t' read -r f idx m z tags; do
  [ -n "$f" ] || continue
  if [ $first -eq 0 ]; then printf "," >> "$OUT"; fi
  first=0
  printf "{\\"fermion\\":\\"%s\\",\\"index\\":%s,\\"mass_GeV\\":%s,\\"logZ\\":%s,\\"tags\\":\\"%s\\"}" "$f" "$idx" "$m" "$z" "$tags" >> "$OUT"
done
printf "]}" >> "$OUT"
echo "wrote $OUT"
