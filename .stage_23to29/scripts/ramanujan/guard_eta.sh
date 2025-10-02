#!/usr/bin/env bash
set -euo pipefail; set +H
LED="analysis/ramanujan/FROZEN_ETA.txt"
REC_DIR="ramanujan/receipts"
[ -f "$LED" ] || { echo "missing $LED"; exit 2; }
ec=0
while IFS= read -r line; do
  case "$line" in \#*|"") continue;; esac
  IFS="|" read -r id expr sb shaline <<<"$line"
  id=$(echo "$id" | xargs); expr=$(echo "$expr" | xargs); sb=$(echo "$sb" | xargs); want=$(echo "$shaline" | xargs | sed "s/^sha256://")
  # find a witness by convention: newest eta receipt, or an override mapping file if present
  wf=""
  map="analysis/ramanujan/witness_map_id_${id}.txt"
  if [ -f "$map" ]; then wf=$(cat "$map")
  else wf=$(ls -1t "$REC_DIR"/eta_*.tsv 2>/dev/null | head -n 1)
  fi
  if [ -z "${wf:-}" ] || [ ! -f "$wf" ]; then echo "ID $id: no witness file found"; ec=1; continue; fi
  got=$(sha256sum "$wf" | awk "{print \$1}")
  if [ "$got" != "$want" ]; then
    echo "SHA DRIFT: id=$id expr=\"$expr\" sturm=$sb file=$wf" ; echo "  expected $want"; echo "  got      $got"; ec=1
  else
    echo "OK id=$id  ($expr)  sturm=$sb"
  fi
done < "$LED"
exit "$ec"
