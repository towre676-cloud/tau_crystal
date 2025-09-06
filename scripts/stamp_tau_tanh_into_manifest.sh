#!/usr/bin/env bash
set -euo pipefail
ROOT="${ROOT:-$HOME/Desktop/tau_crystal/tau_crystal}"
cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }

MAN="docs/manifest.md"
[ -f "$MAN" ] || { echo "[warn] $MAN missing; nothing to stamp"; exit 0; }
[ -s .tau_ledger/TAU_TANH2_SHA256 ] || { echo "[warn] TAU_TANH2_SHA256 missing; run scripts/run_tau_tanh_demo.sh first"; exit 0; }

SHA=$(tr -d ' \r\n' < .tau_ledger/TAU_TANH2_SHA256)

# no-op if line exists
grep -qiE "^TAU_TANH2_SHA256:[[:space:]]*$SHA$" "$MAN" && { echo "[skip] manifest already stamped"; exit 0; }

TMP="$(mktemp)"
awk -v sha="$SHA" '
  BEGIN{ins=0}
  {
    print
    if (ins==0 && tolower($0) ~ /^#.*τ.*crystal.*manifest/){
      print ""
      print "TAU_TANH2_SHA256: " sha
      ins=1
    }
  }
  END{ if(ins==0){ print ""; print "TAU_TANH2_SHA256: " sha } }
' "$MAN" > "$TMP" && mv "$TMP" "$MAN"

echo "[OK] stamped TAU_TANH2_SHA256 into $MAN"
exit 0
