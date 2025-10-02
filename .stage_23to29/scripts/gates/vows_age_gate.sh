#!/usr/bin/env bash
set -euo pipefail; umask 022
file=".tau_ledger/vows/latest.tsv"
max_days="${VOWS_MAX_DAYS:-30}"
[ -f "$file" ] || { echo "[VOWS] missing $file"; exit 0; }

now=$(date -u +%s)
fail=0
while IFS=$'\t' read -r when area vow status; do
  # skip header lines if present
  [[ "$when" =~ ^[0-9]{8}T[0-9]{6}Z$ ]] || continue
  [ "$status" = "open" ] || continue
  # parse YYYYmmddTHHMMSSZ
  if secs=$(date -u -d "${when:0:4}-${when:4:2}-${when:6:2} ${when:9:2}:${when:11:2}:${when:13:2}Z" +%s 2>/dev/null); then
    age_days=$(( (now - secs) / 86400 ))
    if [ "$age_days" -gt "$max_days" ]; then
      echo "[VOWS] open too old ($age_days d): $area :: $vow"
      fail=1
    fi
  else
    echo "[VOWS] unparsable timestamp: $when"
  fi
done < "$file"

[ "$fail" = "0" ] && echo "[VOWS] ok (all open vows within ${max_days}d)" || exit 2
