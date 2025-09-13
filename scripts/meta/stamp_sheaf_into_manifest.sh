#!/usr/bin/env bash
set -Eeuo pipefail; set +H
D=$(cat .tau_ledger/sheaf.digest) || exit 1
STAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
OUT=docs/manifest.md; TMP=docs/manifest.tmp.$$; : > "$TMP"
awk '/^## sheaf_digest \(v1\)/{exit} {print}' "$OUT" > "$TMP"
echo "## sheaf_digest (v1)" >> "$TMP"; echo "" >> "$TMP"; echo "digest: $D" >> "$TMP"
echo "stamped_utc: $STAMP" >> "$TMP"; echo "" >> "$TMP"; mv "$TMP" "$OUT"
