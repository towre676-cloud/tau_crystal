#!/usr/bin/env bash
set -euo pipefail
fail(){ echo "ERROR: $*"; exit 1; }
COMP="analysis/geom/canonical_companions.tsv"
[ -f "$COMP" ] || fail "Missing $COMP"
while IFS=$'\t' read -r hash path; do
  [ -z "$hash" ] && continue
  [ -z "$path" ] && continue
  [ -f "$path" ] || fail "Missing companion file: $path"
  got=$(sha256sum "$path" | awk '{print $1}')
  want="${hash#sha256:}"
  [ "$got" = "$want" ] || fail "SHA mismatch for $path: got $got want $want"
done < "$COMP"
echo "Companions OK."
