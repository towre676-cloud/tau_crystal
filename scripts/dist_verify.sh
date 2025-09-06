#!/usr/bin/env bash
set -euo pipefail
REL="${1:-v0.1.1}"
TARBALL="dist/tau_crystal-$REL.tgz"
[ -s "$TARBALL" ] || { echo "[FAIL] $TARBALL missing"; exit 1; }
sha="$(sha256sum "$TARBALL" | cut -d" " -f1)"
echo "[sha256] sha256:$sha"
if command -v cosign >/dev/null 2>&1 && [ -s "$TARBALL.sig" ] && [ -s "$TARBALL.cert" ]; then
  cosign verify-blob --certificate "$TARBALL.cert" --signature "$TARBALL.sig" "$TARBALL"
  echo "[OK] cosign verify-blob PASS"
else
  echo "[info] cosign artifacts not present; sha256 above is your proof input"
fi
