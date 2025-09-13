#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/holo"
hid=$(sed -n "/^## holography (v1)$/,/^## / s/^id: //p" "$man" | head -n 1)
hwant=$(sed -n "/^## holography (v1)$/,/^## / s/^tensor_sha256: //p" "$man" | head -n 1)
[ -n "${hid:-}" ] && [ -n "${hwant:-}" ] || { echo "::error ::holography section missing"; exit 1; }
j="$dir/$hid.json"; s="$dir/$hid.sha256"; [ -f "$j" ] && [ -f "$s" ] || { echo "::error ::missing $j or $s"; exit 1; }
have=$(cat "$s")
[ "$have" = "$hwant" ] && echo "OK: holography tensor verified" || { echo "FAIL: holo sha mismatch"; echo "want $hwant"; echo "have $have"; exit 1; }
