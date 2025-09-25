#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -e
MAPS=".tau_ledger/runtime/virtualalloc_maps.tsv"
[ -s "$MAPS" ] || { echo "[OK] No unauthorized +X mappings (no maps yet)"; exit 0; }
awk -F'\t' '($0 !~ /^#/) && ($3 == "+X") && ($5 != "capsule"){
  print "[TAINTED] Executable range lacks capsule lineage:", $0; bad=1
} END { if (bad) exit 77; else print "[OK] No unauthorized +X mappings" }' "$MAPS"
