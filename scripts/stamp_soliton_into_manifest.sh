#!/usr/bin/env bash
set -euo pipefail
ROOT="${ROOT:-$HOME/Desktop/tau_crystal/tau_crystal}"
cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }

MAN="docs/manifest.md"
[ -f "$MAN" ] || { echo "[warn] $MAN missing; nothing to stamp"; exit 0; }

[ -s .tau_ledger/SOLITON_SHA256 ] || { echo "[warn] .tau_ledger/SOLITON_SHA256 missing; run scripts/run_soliton_envelope.sh first"; exit 0; }
SHA=$(tr -d ' \r\n' < .tau_ledger/SOLITON_SHA256)

# If the exact line already exists, do nothing
grep -qiE "^SOLITON_SHA256:[[:space:]]*$SHA$" "$MAN" && { echo "[skip] manifest already stamped"; exit 0; }

# Insert under the first header line matching 'τ-Crystal Manifest' or append at end
TMP="$(mktemp)"
awk -v sha="$SHA" '
  BEGIN{ins=0}
  {
    print
    if (ins==0 && tolower($0) ~ /^#.*τ.*crystal.*manifest/){
      print ""
      print "SOLITON_SHA256: " sha
      ins=1
    }
  }
  END{ if(ins==0){ print ""; print "SOLITON_SHA256: " sha } }
' "$MAN" > "$TMP" && mv "$TMP" "$MAN"

echo "[OK] stamped SOLITON_SHA256 into $MAN"
exit 0
