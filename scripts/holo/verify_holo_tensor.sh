#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/holo"
j=$(ls -1 "$dir"/holov1-*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$j" ] || { echo "[err] no holo tensor json"; exit 2; }
holo_sha=$(sed -n "/^## holo (v1)$/,/^## / s/^sha256: //p" "$man" | head -n 1)
[ -n "$holo_sha" ] || { echo "[err] holo section missing in manifest"; exit 2; }
have=$(scripts/meta/_sha256.sh "$j")
[ "$have" = "$holo_sha" ] || { echo "[FAIL] holo tensor hash mismatch"; echo "want: $holo_sha"; echo "have: $have"; exit 1; }
while IFS= read -r line; do
  case "$line" in *file:*) file=$(echo "$line" | sed -E "s/.*\"file\": \"([^\"]+)\".*/\1/"); sha=$(echo "$line" | sed -E "s/.*\"sha256\": \"([^\"]+)\".*/\1/") ;; esac
  [ -s ".tau_ledger/receipts/$file" ] || { echo "[FAIL] missing receipt: $file"; exit 1; }
  have_sha=$(scripts/meta/_sha256.sh ".tau_ledger/receipts/$file")
  [ "$have_sha" = "$sha" ] || { echo "[FAIL] receipt $file hash mismatch"; echo "want: $sha"; echo "have: $have_sha"; exit 1; }
done < <(grep "\"file\":" "$j" | sed "s/^[[:space:]]*//")
echo "[OK] holo tensor verified"
