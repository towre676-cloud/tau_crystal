#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 | cut -d" " -f1; else openssl dgst -sha256 | awk "{print \$2}"; fi; }
fail(){ echo "[verify] $*" >&2; exit 2; }
./scripts/ops/assure_strict.sh >/dev/null
last=$(tail -n1 ./.tau_ledger/CHAIN)
h="${last%%$'\t'*}" ; p="${last#*$'\t'}"
[ -s "$p" ] || fail "missing receipt $p"
hs=$(cat "$p" | sha)
[ "$hs" = "$h" ] || fail "receipt hash mismatch: $hs != $h"
prev=$(jq -r .prev "$p" 2>/dev/null || sed -n 's/.*"prev":"\([^"]*\)".*/\1/p' "$p")
if [ -n "$prev" ]; then
  pl=$(tail -n2 ./.tau_ledger/CHAIN | head -n1 | awk "{print \$1}")
  [ "$pl" = "$prev" ] || fail "chain link mismatch: prev=$prev chain=$pl"
fi
echo "[ok] offline verification passed: $p"
