#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
bash scripts/langlands/hecke_11a1.sh
jq -e '.pass == true' analysis/hecke_11a1_receipt.json >/dev/null
echo "[gate:11a1] OK"
