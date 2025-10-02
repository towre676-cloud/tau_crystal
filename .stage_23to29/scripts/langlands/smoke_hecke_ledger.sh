#!/usr/bin/env bash
set -E -o pipefail; set +H
LEDGER=".tau_ledger/langlands/ap_stable.json"
if ! command -v jq >/dev/null 2>&1; then echo "[smoke] jq not found"; exit 2; fi
if [ ! -s "$LEDGER" ]; then echo "[smoke] missing Hecke ledger: $LEDGER"; exit 3; fi
if ! jq -e 'has("hecke_eigenvalues") and (.hecke_eigenvalues|type=="object" and (.|length>0))' "$LEDGER" >/dev/null 2>&1; then
  echo "[smoke] ledger present but .hecke_eigenvalues is missing/empty"; exit 4
fi
echo "[smoke] Hecke ledger OK: $LEDGER"
