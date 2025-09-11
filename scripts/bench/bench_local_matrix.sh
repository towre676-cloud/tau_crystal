#!/usr/bin/env bash
set -Eeuo pipefail; set +H
N="${1:-5}"
i=1; while [ "$i" -le "$N" ]; do scripts/bench/bench_record.sh cold local; i=$((i+1)); done
i=1; while [ "$i" -le "$N" ]; do scripts/bench/bench_record.sh warm local; i=$((i+1)); done
echo "[bench] local matrix complete: N=$N per mode (warm,cold)"
