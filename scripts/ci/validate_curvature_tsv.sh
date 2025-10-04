#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
LEDGER_DIR=${LEDGER_DIR:-.tau_ledger}
fail=0
for f in "$LEDGER_DIR"/*_curvature.tsv; do
  [ -f "$f" ] || continue
  lineno=0
  while IFS= read -r line || [ -n "$line" ]; do
    lineno=$((lineno+1))
    key=$(printf "%s" "$line" | cut -f1)
    val=$(printf "%s" "$line" | cut -f2)
    if [ -z "$key" ] || ! printf "%s\n" "$val" | grep -Eq "^[-+]?([0-9]*\.)?[0-9]+$"; then
      echo "[error] Malformed TSV: $f:$lineno → $line" >&2
      fail=1
    fi
  done < "$f"
done
exit "$fail"
