#!/usr/bin/env bash
set +H
. scripts/plumbing/_lib.sh || exit 1
BOX="${1:?box}"; KIND="${2:-cm-sector}"
stamp=".tau_ledger/hysteresis/$BOX/${KIND}_receipt.json"
cplx=".tau_ledger/hysteresis/$BOX/hysteresis.json"
csha=""; [ -f "$cplx" ] && csha=$(sha256 "$cplx")
plist=".tau_ledger/tmp/.p.list"; : > "$plist"
for k in .tau_ledger/hysteresis/"$BOX"/p*/hysteresis_p.json; do [ -f "$k" ] && printf "%s %s\n" "$k" "$(sha256 "$k")" >> "$plist"; done
write_json "$stamp" "box" "$BOX" "kind" "$KIND" "ts" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "sha_complex" "$csha" "@p_hashes" "@$plist"
log "receipt_emit: $BOX -> $stamp"
