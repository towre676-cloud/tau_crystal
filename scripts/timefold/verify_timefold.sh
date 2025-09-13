#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; root=".tau_ledger/timefolds"
arc=$(sed -n "/^## timefold (v1)$/,/^## / s/^archive: //p" "$man" | head -n 1)
want=$(sed -n "/^## timefold (v1)$/,/^## / s/^sha256: //p" "$man" | head -n 1)
[ -n "${arc:-}" ] && [ -n "${want:-}" ] || { echo "::error ::timefold section missing"; exit 1; }
path="$root/$arc"; [ -f "$path" ] || { echo "::error ::missing archive $path"; exit 1; }
have=$(scripts/meta/_sha256.sh "$path")
[ "$have" = "$want" ] && echo "OK: timefold archive verified" || { echo "FAIL: timefold hash mismatch"; echo "want $want"; echo "have $have"; exit 1; }
