#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/experimental"; mkdir -p "$root" ".tau_ledger/digests"
log=".tau_ledger/truncation.log"; : > "$log"
shabin="scripts/meta/_sha256.sh"; canon="scripts/experimental/_canonicalize_json.py"
sym2="scripts/experimental/run_sym2.sh"; [ -x "$sym2" ] && "$sym2" || true
for j in "$root"/*.json; do
  [ -s "$j" ] || continue
  tmp="$j.__stamp__"; cp -f "$j" "$tmp"
  if [ -x scripts/experimental/_stamp_provenance.py ]; then
    python scripts/experimental/_stamp_provenance.py "$tmp"
  fi
  if ! python "$canon" "$tmp" 2>>"$log"; then
    echo "[ERR] canonicalize failed: $j" >&2; rm -f "$tmp"; continue
  fi
  mv -f "$tmp" "$j"
  if [ -x scripts/experimental/_validate_schema.py ]; then
    if ! python scripts/experimental/_validate_schema.py "$j"; then echo "[ERR] schema: $j" >&2; exit 7; fi
  fi
  d=$($shabin "$j"); printf "%s  %s\n" "$d" "${j#./}" > ".tau_ledger/digests/$(basename "$j").sha256"
done
[ -s "$log" ] && { echo "[warn] truncation issues recorded in $log" >&2; exit 8; } || true
