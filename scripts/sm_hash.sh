#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mode=$(tr -d "
" < docs/sm_complete/NEUTRINO_TOGGLE.txt)
tmp=$(mktemp)
printf "neutrino_mode=
" "$mode" > "$tmp"
h1=$(sha256sum -b docs/sm_complete/SM_COMPLETE.md | cut -d" " -f1)
h2=$(sha256sum -b "$tmp" | cut -d" " -f1)
printf "%s%s
" "$h1" "$h2" | sha256sum -b | cut -d" " -f1 > receipts/sm_complete/SM_COMPLETE.sha256
rm -f "$tmp"
