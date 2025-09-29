#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
mkdir -p .tau_ledger/cohomology .cache
COC=".tau_ledger/cohomology/cocycle_tau.json"
COB=".tau_ledger/cohomology/coboundary_delta_tau.json"
H1=".tau_ledger/cohomology/h1_obstruction.json"
SHA=".tau_ledger/cohomology/h1_obstruction.sha256"
: > "$COC"; echo "[" >> "$COC"
tau=(1.0000 0.5403 0.8576 0.6543 0.7937 0.7074)
for i in "${!tau[@]}"; do
  sep=","; [ "$i" = 0 ] && sep=""
  printf "%s%.6f" "$sep" "${tau[$i]}" >> "$COC"
done; echo "]" >> "$COC"
: > "$COB"; echo "[" >> "$COB"
for ((i=0; i<${#tau[@]}-1; i++)); do
  a="${tau[$i]}"
  b="${tau[$((i+1))]}"
  d=$(printf "%.6f" "$(echo "$b - $a" | bc -l)")
  sep=","; [ "$i" = 0 ] && sep=""
  printf "%s%s" "$sep" "$d" >> "$COB"
done; echo "]" >> "$COB"
: > "$H1"; echo "[" >> "$H1"
mapfile -t delta < "$COB" < <(tr -d "[], " < "$COB")
for ((i=0; i<${#delta[@]}-1; i++)); do
  d1="${delta[$i]}"
  d2="${delta[$((i+1))]}"
  diff=$(printf "%.6f" "$(echo "$d2 - $d1" | bc -l)")
  sep=","; [ "$i" = 0 ] && sep=""
  printf "%s%s" "$sep" "$diff" >> "$H1"
done; echo "]" >> "$H1"
if command -v sha256sum >/dev/null 2>&1; then sha256sum "$H1" > "$SHA";
else openssl dgst -sha256 "$H1" | awk "{print \$2}" > "$SHA"; fi
echo "[ok] H1 obstruction capsule written → $H1"
