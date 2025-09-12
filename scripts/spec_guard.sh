#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
status=0
shopt -s nullglob
found=0
for m in .tau_ledger/**/*.json .tau_ledger/*.json receipts/**/*.json receipts/*.json docs/**/*.json; do
  [ -f "$m" ] || continue; found=1
  if ! grep -q '\"tau_class\"":' "$m"; then echo "::error file=$m::missing tau_class"; status=1; fi
  if grep -q '\"tau_class\"[[:space:]]*:[[:space:]]*\"spectral"" "$m"; then
    if ! grep -q '\"operator\"":' "$m" && ! ls .tau_ledger/operator.json >/dev/null 2>&1; then echo "::error file=$m::spectral τ missing operator provenance"; status=1; fi
  fi
  if ! grep -q '\"provenance\"":' "$m"; then echo "::error file=$m::missing provenance"; status=1; fi
done
if [ "$found" -eq 0 ]; then echo "::notice::no receipts found"; fi
exit "$status"
