#!/usr/bin/env bash
set -euo pipefail; set +H
REC="${1:?path to receipt.json}"
C="$(scripts/bin/find_contract_by_hash.sh "$REC" 2>/dev/null || true)"
if [ -n "$C" ]; then
  python3 scripts/bin/receipt_set_contract.py "$REC" "$C"
  echo "[ok] embedded contract_path: $C"
else
  echo "[warn] could not resolve contract from hash; pass explicit path to verify_receipt.sh"
fi
scripts/bin/verify_receipt.sh "$REC" "${C:-}"
