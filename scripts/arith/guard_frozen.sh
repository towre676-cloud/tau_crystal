#!/usr/bin/env bash
set -euo pipefail
fail(){ echo "ERROR: $*"; exit 1; }
LEDGER="analysis/arith/FROZEN.hashes.tsv"
[ -f "$LEDGER" ] || fail "Missing $LEDGER"
while IFS=$'\t' read -r hash path; do
  [ -z "$hash" ] && continue
  [ -z "$path" ] && continue
  [ -f "$path" ] || fail "Frozen file missing: $path"
  got=$(sha256sum "$path" | awk '{print $1}')
  want="${hash#sha256:}"
  [ "$got" = "$want" ] || fail "Frozen SHA mismatch for $path: got $got want $want"
done < "$LEDGER"
echo "Frozen determinants OK."
