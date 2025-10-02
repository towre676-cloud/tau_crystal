#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/holo"
j=$(ls -1 "$dir"/holov1-*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$j" ] || { echo "[err] no holo tensor json; run build_holo_tensor.sh"; exit 2; }
holo_sha=$(sed -n "/^## holo (v1)$/,/^## / s/^sha256: //p" "$man" | head -n 1)
[ -n "$holo_sha" ] || { echo "[err] holo section missing in manifest"; exit 2; }
have=$(scripts/sha256.sh "$j")
[ "$have" = "$holo_sha" ] || { echo "[FAIL] holo tensor hash mismatch; want: $holo_sha, have: $have"; exit 1; }
while IFS= read -r line; do
  [ -n "$line" ] || continue
  file=$(echo "$line" | jq -r .file)
  sha=$(echo "$line" | jq -r .sha256)
  [ -n "$file" ] && [ -n "$sha" ] || { echo "[FAIL] invalid tensor entry: $line"; exit 1; }
  [ -s ".tau_ledger/receipts/$file" ] || { echo "[FAIL] missing receipt: $file"; exit 1; }
  have_sha=$(scripts/sha256.sh ".tau_ledger/receipts/$file")
  [ "$have_sha" = "$sha" ] || { echo "[FAIL] receipt $file hash mismatch; want: $sha, have: $have_sha"; exit 1; }
done < <(jq -c ".receipts[]" "$j")
echo "[OK] holo tensor verified"
