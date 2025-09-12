#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root="${1:-$PWD}"
sha_now="$(bash "$(dirname "$0")/hash_action_wrapper.sh" "$root" | tail -n1)"
read_digest() {
  f="$1"
  if [ -s "$f" ]; then
    if command -v jq >/dev/null 2>&1; then
      jq -r '."action_wrapper_sha" // empty' "$f"
    else
      grep -oE '"action_wrapper_sha"[[:space:]]*:[[:space:]]*"[^"]*"' "$f" | sed -E 's/.*:"([^"]*)".*/\1/' | head -n1
    fi
  fi
}
sha_stored="$(read_digest ".tau_ledger/receipt.json")"
[ -n "$sha_stored" ] || sha_stored="$(read_digest "tau-crystal-manifest.json")"
[ -n "$sha_stored" ] || { echo "::error::missing action_wrapper_sha in receipt/manifest"; exit 10; }
[ "$sha_now" = "$sha_stored" ] || { echo "::error::wrapper digest mismatch"; echo "now=$sha_now stored=$sha_stored"; exit 12; }
echo "[OK] wrapper digest enforced: $sha_now"
