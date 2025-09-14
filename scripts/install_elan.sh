#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
url="https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"
expected_sha="expected_sha256_here"  # Replace with actual hash
tmp=$(mktemp); trap "rm -f \"$tmp\"" EXIT
curl -sSfL "$url" -o "$tmp"
sha=$(scripts/sha256.sh "$tmp")
[ "$sha" = "$expected_sha" ] || { echo "[err] $0: operation failed; check input and try again
sh "$tmp" -y
echo "[OK] installed elan"
