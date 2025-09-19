#!/usr/bin/env bash
set -E -o pipefail; set +H
[ -x scripts/langlands/smoke_hecke_ledger.sh ] || { echo "[strict] missing smoke script"; exit 10; }
bash scripts/langlands/smoke_hecke_ledger.sh
[ -x scripts/langlands/run_phase_next.sh ] || { echo "[strict] missing run_phase_next.sh"; exit 11; }
bash scripts/langlands/run_phase_next.sh
