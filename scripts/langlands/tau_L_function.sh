#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
seqfile="${1:-.tau_ledger/seq/tau.csv}"
out=".tau_ledger/langlands/L_tau.json"
mkdir -p ".tau_ledger/langlands"
[ -s "$seqfile" ] || { echo "{\"status\":\"no_tau\",\"grid\":[0.8,0.9,1.0,1.1],\"L\":[],\"zeros\":[]}" > "$out"; echo "$out"; exit 0; }
echo "{\"status\":\"stub\",\"grid\":[0.8,0.9,1.0,1.1],\"L\":[1.0,1.0,1.0,1.0],\"zeros\":[]}" > "$out"
echo "$out"
