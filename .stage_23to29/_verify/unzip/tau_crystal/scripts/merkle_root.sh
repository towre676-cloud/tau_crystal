#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger"; mkdir -p "$root"
tmp=$(mktemp); trap "rm -f \"$tmp\"" EXIT
while IFS= read -r f; do
  file_type=$(file -b --mime-type "$f")
  case "$file_type" in application/*|image/*|video/*) ;; *) sha256sum "$f" >> "$tmp" ;; esac
done < <(find . -type f | sort)
scripts/sha256.sh "$file"
if command -v openssl >/dev/null 2>&1; then
  openssl dgst -sha256 -sign "$root/private_key.pem" "$root/merkle_root.txt" > "$root/merkle_root.sig"
fi
echo "[OK] merkle root: $(cat "$root/merkle_root.txt")"
# Cache previous level hashes
if [ -f "$root/merkle_cache.txt" ]; then
  mv "$root/merkle_cache.txt" "$tmp"
fi
