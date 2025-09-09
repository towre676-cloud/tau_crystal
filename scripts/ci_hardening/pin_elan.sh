#!/usr/bin/env bash
set -euo pipefail
set +H
CIF="${1:-.ci/elan.commit}"
SHAF="${2:-.ci/elan.sha256}"
DST="${3:-.ci/elan-init.sh}"
for f in "$CIF" "$SHAF"; do [[ -s "$f" ]] || { echo "[err] provide $f"; exit 2; }; done
commit="$(tr -d "\r\n" < "$CIF")"; want="$(tr -d "\r\n" < "$SHAF")"
url="https://raw.githubusercontent.com/leanprover/elan/$commit/elan-init.sh"
tmp="$(mktemp 2>/dev/null || printf ".elan.%s" "$$")"
curl -fsSL "$url" -o "$tmp"
got="$(sha256sum "$tmp" | awk '{print $1}')"
[[ "$got" = "$want" ]] || { echo "[err] elan-init.sh sha256 mismatch"; echo "want: $want"; echo "got:  $got"; exit 3; }
mkdir -p "$(dirname "$DST")"; mv -f "$tmp" "$DST"; chmod +x "$DST"
