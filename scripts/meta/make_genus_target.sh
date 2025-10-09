#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
CD="$HOME/Desktop/tau_crystal/tau_crystal"
cd "$CD" || exit 1
T="$1"; [ -n "$T" ] || { echo "usage: make_genus_target.sh <TARGET_ID>" >&2; exit 2; }
C="receipts/genus/${T}_coeffs.json"
O="receipts/genus/${T}_observation.json"
d=$(dirname "$C"); [ -d "$d" ] || mkdir -p "$d"
> "$C"
printf "%s\n" "{" >> "$C"
printf "%s\n" "  \"schema\": \"tau_crystal.elliptic_genus.coeffs.v1\"," >> "$C"
printf "%s\n" "  \"surface\": \"${T}\"," >> "$C"
printf "%s\n" "  \"generic\": []," >> "$C"
printf "%s\n" "  \"twisted\": []" >> "$C"
printf "%s\n" "}" >> "$C"
> "$O"
printf "%s\n" "{" >> "$O"
printf "%s\n" "  \"schema\": \"tau_crystal.elliptic_genus.v1\"," >> "$O"
printf "%s\n" "  \"surface\": \"${T}\"," >> "$O"
printf "%s\n" "  \"generic\": {\"zero_modes\": 0}," >> "$O"
printf "%s\n" "  \"twisted\": {\"zero_modes\": 0}" >> "$O"
printf "%s\n" "}" >> "$O"
printf "%s\n" "$C"
