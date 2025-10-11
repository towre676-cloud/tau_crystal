#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
ref=$(tr -d '\r\n' < receipts/sm_complete/SM_COMPLETE.sha256)
mode_file="docs/sm_complete/NEUTRINO_TOGGLE.txt"
[ -f "$mode_file" ] || { echo "Missing toggle file"; exit 1; }
tmp=$(mktemp)
printf "neutrino_mode=%s\n" "$(tr -d '\r\n' < "$mode_file")" > "$tmp"
h_core=$(sha256sum -b docs/sm_complete/SM_COMPLETE.md | awk '{print $1}')
h_mode=$(sha256sum -b "$tmp" | awk '{print $1}')
h_params=$( [ -f docs/sm_complete/params.json ] && sha256sum -b docs/sm_complete/params.json | awk '{print $1}' || echo 0 )
h_norm=$( [ -f docs/sm_complete/NORMALIZATION_MF.md ] && sha256sum -b docs/sm_complete/NORMALIZATION_MF.md | awk '{print $1}' || \
          [ -f docs/sm_complete/NORMALIZATION_MANIFEST.md ] && sha256sum -b docs/sm_complete/NORMALIZATION_MANIFEST.md | awk '{print $1}' || echo 0 )
now=$(printf "%s%s%s%s" "$h_core" "$h_mode" "$h_params" "$h_norm" | sha256sum -b | awk '{print $1}')
rm -f "$tmp"
test "$ref" = "$now" && echo OK || { echo FAIL; exit 1; }
