#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
[ -s POISON ] || { echo "[poison] missing POISON"; exit 13; }
prev=$(tail -n2 .tau_ledger/CHAIN | head -n1 | awk '{print $1}')
got=$(tr -d '\r\n' < POISON)
[ "$got" = "$prev" ] || { echo "[poison] mismatch: POISON=$got prev=$prev"; exit 14; }
echo "[poison] OK"
