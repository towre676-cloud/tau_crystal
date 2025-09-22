#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
set +e; files=$(ls -1 .tau_ledger/genius/entangle-*.meta 2>/dev/null | LC_ALL=C sort); rc=$?; set -e
[ $rc -eq 0 ] && [ -n "$files" ] || { echo "[err] no entangled receipts"; exit 2; }
sum=$(awk '/^tau: /{s+=$2} END{print s+0}' $files)
cnt=$(awk '/^tau: /{n++} END{print n+0}' $files)
[ "$cnt" -gt 0 ] || { echo "[err] no tau values"; exit 2; }
ok=$(awk -v s="$sum" -v n="$cnt" 'BEGIN{print (s>(0.5*n))?1:0}')
[ "$ok" = "1" ] && echo "[OK] entanglement verified" || { echo "[FAIL] entanglement"; exit 1; }
