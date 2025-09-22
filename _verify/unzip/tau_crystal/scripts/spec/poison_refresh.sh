#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
bash scripts/ops/verify_offline.sh >/dev/null
prev=$(tail -n2 .tau_ledger/CHAIN | head -n1 | awk '{print $1}')
printf "%s\n" "$prev" > POISON
git add POISON
git diff --cached --quiet || git commit -m "poison: refresh to prev head $(printf %.7s "$prev")"
