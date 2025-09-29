#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
TS="docs/ledger/timefold_receipt.json"; LS="docs/ledger/langlands_capsule.json"
: > "$TS"; : > "$LS"
now=$(date -u +%Y-%m-%dT%H:%M:%SZ)
printf "{" >> "$TS"; printf "\"kind\":\"TimefoldReceipt\",\"sealed_at\":\"%s\"" "$now" >> "$TS"; printf "}\n" >> "$TS"
printf "{" >> "$LS"; printf "\"kind\":\"LanglandsCapsule\",\"sealed_at\":\"%s\"" "$now" >> "$LS"; printf "}\n" >> "$LS"
