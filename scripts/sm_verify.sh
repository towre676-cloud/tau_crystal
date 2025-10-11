#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
ref=$(tr -d "
" < receipts/sm_complete/SM_COMPLETE.sha256)
mode=$(tr -d "
" < docs/sm_complete/NEUTRINO_TOGGLE.txt)
tmp=$(mktemp)
printf "neutrino_mode=
" "$mode" > "$tmp"
h1=$(sha256sum -b docs/sm_complete/SM_COMPLETE.md | cut -d" " -f1)
h2=$(sha256sum -b "$tmp" | cut -d" " -f1)
now=$(printf "%s%s
" "$h1" "$h2" | sha256sum -b | cut -d" " -f1)
rm -f "$tmp"
test "$ref" = "$now" && echo OK || { echo FAIL; exit 1; }
