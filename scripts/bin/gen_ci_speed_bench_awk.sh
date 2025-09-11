#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
src=".tau_ledger/bench/runs.ndjson"
out="docs/benchmarks/ci_speed.md"
mkdir -p "$(dirname "$out")"
if [ ! -s "$src" ]; then printf "%s\n\n" "# CI speed benchmarks (receipt-backed)" > "$out"; echo "No runs yet." >> "$out"; exit 0; fi
awk -f scripts/bin/bench_ci_speed.awk "$src" > "$out"
