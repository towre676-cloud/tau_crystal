#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LED=".tau_ledger/freed"; mkdir -p "$LED"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
OUT="$LED/phi_pullback_$STAMP.json"
python scripts/freed/phi_pullback_check.py "$OUT"
jq -r ".equation + \" :: pass=\" + ( .pass|tostring ) + \" :: max_errs=\" + ([.results[].max_abs_error]|max|tostring)" "$OUT" 2>/dev/null || true
