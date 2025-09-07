#!/usr/bin/env bash
set -uo pipefail
set +H
mkdir -p .tau_ledger/debug
TS="$(date +%Y%m%dT%H%M%SZ)"
LOG=".tau_ledger/debug/wrap-$TS.log"
PS4='+ [${BASH_SOURCE##*/}:${LINENO}] '; exec > >(tee -a "$LOG") 2>&1; set -x
echo "[wrap] pwd: $(pwd)"
