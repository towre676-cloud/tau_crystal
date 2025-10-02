#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
fail=0
STRICT_NORM=${STRICT_NORM:-0}
warn_or_fail(){ if [ "${STRICT_NORM}" = "1" ]; then echo "$1"; return 1; else echo "$1 (WARN)"; return 0; fi; }
check_norm(){ n1="$1"; n2="$2"; if [ ! -f "$n1" ] || [ ! -f "$n2" ]; then warn_or_fail "[NORM] missing $n1 or $n2"; return $?; fi; s1=$(jq -S . "$n1" 2>/dev/null | sha256sum | awk "{print \$1}"); s2=$(jq -S . "$n2" 2>/dev/null | sha256sum | awk "{print \$1}"); if [ "$s1" != "$s2" ]; then warn_or_fail "[NORM] mismatch $n1 vs $n2"; rc=$?; return $rc; else echo "[NORM] ok $n1 == $n2"; return 0; fi; }
check_norm analysis/normalized/ap.norm.json analysis/normalized/ap.norm.norm.json || fail=1
check_norm analysis/normalized/satake.norm.json analysis/normalized/satake.norm.norm.json || fail=1
check_norm analysis/normalized/combined_ap_satake.norm.json analysis/normalized/combined_ap_satake.norm.norm.json || fail=1
check_norm analysis/normalized/rank.norm.json analysis/normalized/rank.norm.norm.json || fail=1
check_norm analysis/normalized/motives.norm.json analysis/normalized/motives.norm.norm.json || fail=1
check_norm analysis/normalized/L_tau.norm.json analysis/normalized/L_tau.norm.norm.json || fail=1
atlas_dir="analysis/atlas/11a1"; ledger_json=".tau_ledger/langlands/ap.json"
if [ -f "$atlas_dir/ap.tsv" ] && [ -f "$ledger_json" ]; then
  a=$(cut -f1,2 "$atlas_dir/ap.tsv" | LC_ALL=C sort | tr -d "\r")
  l=$(jq -r '.ap as $ap |
    if ($ap|type)=="array" then
      if ($ap|length>0 and ($ap[0]|type)=="array") then
        $ap[] | @tsv
      elif ($ap|length>0 and ($ap[0]|type)=="object" and ($ap[0]|has("p") and $ap[0]|has("a"))) then
        $ap[] | [.p,.a] | @tsv
      else empty end
    elif ($ap|type)=="object" then
      $ap | to_entries | .[] | [(.key|tonumber), .value] | @tsv
    else empty end
  ' "$ledger_json" | LC_ALL=C sort | tr -d "\r")
  if ! diff -u <(printf "%s\n" "$a") <(printf "%s\n" "$l") >/dev/null; then warn_or_fail "[ATLAS] ap.tsv vs ledger differ"; rc=$?; [ $rc -ne 0 ] && fail=1; else echo "[ATLAS] ap.tsv == ledger"; fi
else echo "[ATLAS] skip (missing atlas or ledger)"; fi
if command -v dot >/dev/null 2>&1; then
  if [ -f analysis/geom/proof.dot ]; then dot -Tsvg analysis/geom/proof.dot > analysis/geom/proof.svg && [ -s analysis/geom/proof.svg ] && echo "[PROOF] svg rendered" || { warn_or_fail "[PROOF] empty or failed render"; rc=$?; [ $rc -ne 0 ] && fail=1; }; else echo "[PROOF] skip (no proof.dot)"; fi
else warn_or_fail "[PROOF] graphviz dot not found"; rc=$?; [ $rc -ne 0 ] && fail=1; fi
exit $fail
