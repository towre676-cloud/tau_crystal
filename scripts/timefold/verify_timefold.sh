#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; root=".tau_ledger/timefolds"
arc=$(awk '/^## timefold 
𝑣
1
v1/{f=1;next} f && /^archive:/{print $2; exit}' "$man")
want=$(awk '/^## timefold 
𝑣
1
v1/{f=1;next} f && /^sha256:/{print $2; exit}' "$man")
[ -n "${arc:-}" ] && [ -n "${want:-}" ] || { echo "::error ::timefold section missing"; exit 1; }
path="$root/$arc"; test -f "$path" || { echo "::error ::missing archive $path"; exit 1; }
have=$(scripts/meta/_sha256.sh "$path")
[ "$have" = "$want" ] && echo "OK: timefold archive verified" || { echo "FAIL: timefold hash mismatch"; echo "want $want"; echo "have $have"; exit 1; }
