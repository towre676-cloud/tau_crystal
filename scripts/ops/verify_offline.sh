#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 | cut -d" " -f1; else openssl dgst -sha256 | awk "{print \$2}"; fi; }
./scripts/ops/assure_strict.sh >/dev/null
last=$(tail -n1 ./.tau_ledger/CHAIN)
h="${last%%$'\t'*}" ; p="${last#*$'\t'}"
[ -s "$p" ] || { echo "[verify] missing receipt $p" >&2; exit 2; }
hs=$(cat "$p" | sha); [ "$hs" = "$h" ] || { echo "[verify] receipt hash mismatch" >&2; exit 2; }
prev=$(sed -n 's/.*"prev":"\([^"]*\)".*/\1/p' "$p")
if [ -n "$prev" ]; then pl=$(tail -n2 ./.tau_ledger/CHAIN | head -n1 | awk "{print \$1}"); [ "$pl" = "$prev" ] || { echo "[verify] chain link mismatch" >&2; exit 2; }; fi
echo "[ok] offline verification passed: $p"
