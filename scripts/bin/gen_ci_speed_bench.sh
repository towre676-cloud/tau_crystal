#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
src=".tau_ledger/bench/runs.ndjson"
out="docs/benchmarks/ci_speed.md"
mkdir -p "$(dirname "$out")"
[ -s "$src" ] || { printf "%s\n\n" "# CI speed benchmarks (receipt-backed)" > "$out"; echo "No runs yet." >> "$out"; exit 0; }
python3 scripts/bin/bench_ci_speed.py "$src" "$out" 2>/dev/null || {
  echo "[warn] python3 missing; writing stub." >&2
  printf "%s\n\n" "# CI speed benchmarks (receipt-backed)" > "$out"; echo "Python not available; cannot compute medians." >> "$out";
}
