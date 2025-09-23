#!/usr/bin/env bash
set -euo pipefail; umask 022
[ "${SEED_INIT:-0}" = "1" ] && return 0
SEED="$(date +%s%N | sha256sum | cut -c1-16)"
export SEED PYTHONHASHSEED="$SEED"
mkdir -p .tau_ledger/seeds
echo "$SEED" > ".tau_ledger/seeds/$(date -u +%Y%m%dT%H%M%SZ).seed"
export SEED_INIT=1
echo "[SEED] $SEED"
