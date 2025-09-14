#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
lin=".tau_ledger/langlands/L_tau.json"
out=".tau_ledger/langlands/rank.json"
mkdir -p ".tau_ledger/langlands"
[ -s "$lin" ] || { echo "{\"status\":\"no_L\",\"rank\":null}" > "$out"; echo "$out"; exit 0; }
echo "{\"status\":\"stub\",\"rank\":0}" > "$out"
echo "$out"
