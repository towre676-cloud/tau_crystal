#!/usr/bin/env bash
set +e; umask 022; export LC_ALL=C LANG=C
BULK="${1:-$(ls -1 analysis/freed/bulk_logdet_*.json 2>/dev/null | tail -n1)}"
ETA="${2:-$(ls -1 analysis/freed/eta_boundary_*.json 2>/dev/null | tail -n1)}"
LOGB="${3:-$(ls -1 analysis/freed/logB_receipt_*.json 2>/dev/null | tail -n1)}"
for p in "$BULK" "$ETA" "$LOGB"; do [ -s "${p:-}" ] || { echo "[skip] APS missing input: $p"; exit 0; }; done
python scripts/freed/aps_equality_check.py "$BULK" "$ETA" "$LOGB"
