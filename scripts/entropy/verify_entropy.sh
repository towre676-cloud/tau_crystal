#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; dir=".tau_ledger/entropy"
eid=$(sed -n "/^## entropy (v1)$/,/^## / s/^id: //p" "$man" | head -n 1)
ewant=$(sed -n "/^## entropy (v1)$/,/^## / s/^entropy_sha256: //p" "$man" | head -n 1)
[ -n "${eid:-}" ] && [ -n "${ewant:-}" ] || { echo "::error ::entropy section missing"; exit 1; }
j="$dir/$eid.json"; s="$dir/$eid.sha256"; [ -f "$j" ] && [ -f "$s" ] || { echo "::error ::missing $j or $s"; exit 1; }
have=$(cat "$s")
[ "$have" = "$ewant" ] && echo "OK: entropy witness verified" || { echo "FAIL: entropy sha mismatch"; echo "want $ewant"; echo "have $have"; exit 1; }
