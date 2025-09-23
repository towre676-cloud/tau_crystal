#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
bash scripts/dev/run_green_logged.sh || true
echo ""; echo "[hold] tailing the latest log; press Ctrl-C to exit"
LOG=$(ls -1t .tau_ledger/logs/fusion_*.log 2>/dev/null | head -n1 || true)
[ -n "$LOG" ] && tail -n 200 -f "$LOG" || { echo "[warn] no log found"; tail -f /dev/null; }
