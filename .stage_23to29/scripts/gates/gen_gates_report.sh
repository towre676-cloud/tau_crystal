#!/usr/bin/env bash
set -euo pipefail; umask 022

strict=${GATES_STRICT:-0}
outdir=".tau_ledger/gates"
mkdir -p "$outdir"
ts="$(date -u +%Y%m%dT%H%M%SZ)"
out="$outdir/report.$ts.txt"

# collect snippets (all optional, never fail if missing)
prog="analysis/progress.tsv"
caps=".tau_ledger/capsules.tsv"
vows=".tau_ledger/vows/latest.tsv"

open_vows="-"
if [ -f "$vows" ]; then
  open_vows="$(awk -F'\t' 'NR>1 && $4=="open"{c++} END{print (c+0)}' "$vows" 2>/dev/null || echo 0)"
fi

{
  echo "# Gates Report"
  echo "# UTC: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo

  echo "== PROGRESS =="
  if [ -f "$prog" ]; then
    # show header + last 10 unique organs by last_ok_utc/error freshness
    awk 'NR==1{print; next} NR>1{print}' "$prog" | tail -n 15
  else
    echo "(no progress.tsv)"
  fi
  echo

  echo "== CAPSULE INDEX (tail) =="
  if [ -f "$caps" ]; then
    tail -n 5 "$caps"
  else
    echo "(no capsules.tsv)"
  fi
  echo

  echo "== VOWS =="
  if [ -f "$vows" ]; then
    echo "open_vows: $open_vows"
    # show last 5 vows lines
    tail -n 5 "$vows"
  else
    echo "(no vows ledger)"
  fi
  echo
} > "$out"

echo "[GATES] wrote $out"

# strict mode: fail if any organ (other than gates) is red
if [ "$strict" = "1" ] && [ -f "$prog" ]; then
  if awk -F'\t' 'NR>1 && $1!="gates" && $2=="fail"{exit 1} END{exit 0}' "$prog"; then
    exit 0
  else
    echo "[GATES] strict mode: other organs red → fail"
    exit 2
  fi
fi

exit 0
