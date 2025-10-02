#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -e
mkdir -p .tau_ledger/heegner .tau_ledger/runtime .tau_ledger/hysteresis .tau_ledger/invariants .cache
[ -s ".tau_ledger/heegner/zone_reference.json" ] || printf '%s\n' '{"entropy_vector":[0.10,0.05,0.03,0.02]}' > .tau_ledger/heegner/zone_reference.json
[ -s ".tau_ledger/runtime/current_entropy.json" ] || printf '%s\n' '{"entropy_vector":[0.10,0.05,0.03,0.02]}' > .tau_ledger/runtime/current_entropy.json
[ -s ".tau_ledger/hysteresis/latest_barcode.json" ] || printf '%s\n' '{"loop_area":0.000}' > .tau_ledger/hysteresis/latest_barcode.json
[ -s ".tau_ledger/hysteresis/barcode_ref.json" ]   || printf '%s\n' '{"loop_area":0.000}' > .tau_ledger/hysteresis/barcode_ref.json
[ -s ".tau_ledger/runtime/virtualalloc_maps.tsv" ] || printf '%s\n' "#start-end\tperms\tflag\tbacking\tlineage" > .tau_ledger/runtime/virtualalloc_maps.tsv
