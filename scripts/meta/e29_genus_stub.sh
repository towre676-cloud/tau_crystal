#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
OUT=receipts/e29_genus_observation.json
> "$OUT"
printf "%s\n" "{" >> "$OUT"
printf "%s\n" "  \"schema\": \"tau_crystal.elliptic_genus.v1\"," >> "$OUT"
printf "%s\n" "  \"surface\": \"Elkies–Klagsbrun K3 fibration\"," >> "$OUT"
printf "%s\n" "  \"note\": \"stub: replace with computed coefficients c(n,r)\"," >> "$OUT"
printf "%s\n" "  \"generic\": {\"zero_modes\": 17}," >> "$OUT"
printf "%s\n" "  \"twisted\": {\"zero_modes\": 29}" >> "$OUT"
printf "%s\n" "}" >> "$OUT"
printf "%s\n" "$OUT"
