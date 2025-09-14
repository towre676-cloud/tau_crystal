#!/usr/bin/env bash
set -Eeuo pipefail; set +H
j=".tau_ledger/signature/$(ls -1 .tau_ledger/signature/sigv1-*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)"
[ -s "$j" ] || { echo "[err] no signature json"; exit 2; }
ok=0; fail=0
while IFS= read -r line; do
  case "$line" in *file:*) file=$(echo "$line" | sed -E "s/.*\"file\": \"([^\"]+)\".*/\1/"); sha=$(echo "$line" | sed -E "s/.*\"sha256\": \"([^\"]+)\".*/\1/") ;; esac
  [ -s "constraints.d/$file" ] || { echo "FAIL: missing $file"; fail=$((fail+1)); continue; }
  have=$(scripts/meta/_sha256.sh "constraints.d/$file")
  [ "$have" = "$sha" ] && { echo "OK: $file"; ok=$((ok+1)); } || { echo "FAIL: $file want=$sha have=$have"; fail=$((fail+1)); }
done < <(grep "\"file\":" "$j" | sed "s/^[[:space:]]*//")
[ "$fail" -eq 0 ] && echo "OK: signature rules verified" || { echo "FAIL: $fail errors"; exit 1; }
