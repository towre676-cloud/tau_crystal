#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
mkdir -p "$LEDGER_DIR"
ts=$(date -u +%Y%m%dT%H%M%SZ 2>/dev/null || date +%Y%m%dT%H%M%SZ)
f="${LEDGER_DIR}/${ts}_curvature.tsv"
: > "$f"
printf "%s\t%s\n" "prelude"  "0.000000030000" >> "$f"
printf "%s\t%s\n" "kernel"   "0.000000020000" >> "$f"
printf "%s\t%s\n" "replay"   "-0.000000010000" >> "$f"
printf "%s\t%s\n" "closure"  "0.000000000000" >> "$f"
echo "[emit] wrote $f"
exit 0
