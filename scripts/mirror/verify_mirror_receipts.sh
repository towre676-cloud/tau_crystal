#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/mirror"
meta=$(ls -1 "$dir"/mirrorv1-*.meta 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "$meta" ] || { echo "[err] no mirror meta found"; exit 2; }
remote=$(sed -n "s/^remote: //p" "$meta" | head -n 1)
want_sha=$(sed -n "/^## mirror (v1)$/,/^## / s/^sha256: //p" "$man" | head -n 1)
have_sha=$(scripts/meta/_sha256.sh "$meta")
[ "$have_sha" = "$want_sha" ] || { echo "[FAIL] mirror meta hash mismatch"; echo "want: $want_sha"; echo "have: $have_sha"; exit 1; }
while IFS= read -r line; do
  case "$line" in *file:*) file=$(echo "$line" | sed -E "s/.*\"file\": \"([^\"]+)\".*/\1/"); sha=$(echo "$line" | sed -E "s/.*\"sha256\": \"([^\"]+)\".*/\1/") ;; esac
  tmp=$(mktemp); curl -s "$remote/.tau_ledger/receipts/$file" -o "$tmp"
  have=$(scripts/meta/_sha256.sh "$tmp")
  [ "$have" = "$sha" ] || { echo "[FAIL] receipt $file hash mismatch"; echo "want: $sha"; echo "have: $have"; rm -f "$tmp"; exit 1; }
  rm -f "$tmp"
done < <(grep "\"file\":" "$meta" | sed "s/^[[:space:]]*//")
echo "[OK] mirror receipts verified from $remote"
