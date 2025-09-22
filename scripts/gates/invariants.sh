#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
fail=0
check_norm(){ n1="$1"; n2="$2";
  if [ ! -f "$n1" ] || [ ! -f "$n2" ]; then echo "[NORM] missing $n1 or $n2"; return 1; fi
  s1=$(jq -S . "$n1" 2>/dev/null | sha256sum | awk "{print \$1}")
  s2=$(jq -S . "$n2" 2>/dev/null | sha256sum | awk "{print \$1}")
  if [ "$s1" != "$s2" ]; then echo "[NORM] mismatch $n1 vs $n2"; return 1; fi
  echo "[NORM] ok $n1 == $n2"
}
check_norm analysis/normalized/ap.norm.json analysis/normalized/ap.norm.norm.json || fail=1
check_norm analysis/normalized/satake.norm.json analysis/normalized/satake.norm.norm.json || fail=1
check_norm analysis/normalized/combined_ap_satake.norm.json analysis/normalized/combined_ap_satake.norm.norm.json || fail=1
check_norm analysis/normalized/rank.norm.json analysis/normalized/rank.norm.norm.json || fail=1
check_norm analysis/normalized/motives.norm.json analysis/normalized/motives.norm.norm.json || fail=1
check_norm analysis/normalized/L_tau.norm.json analysis/normalized/L_tau.norm.norm.json || fail=1
atlas_dir="analysis/atlas/11a1"; ledger_json=".tau_ledger/langlands/ap.json"
if [ -f "$atlas_dir/ap.tsv" ] && [ -f "$ledger_json" ]; then
  a=$(cut -f1,2 "$atlas_dir/ap.tsv" | LC_ALL=C sort | tr -d "\r")
  l=$(jq -r '
    .ap as $ap |
    if ($ap|type)=="array" then
      if ($ap|length>0 and ($ap[0]|type)=="array") then
        $ap[] | @tsv
      elif ($ap|length>0 and ($ap[0]|type)=="object" and ($ap[0]|has("p") and $ap[0]|has("a"))) then
        $ap[] | [.p,.a] | @tsv
      else empty end
    elif ($ap|type)=="object" then
      to_entries | .[] | [(.key|tonumber), .value] | @tsv
    else empty end
  ' "$ledger_json" | LC_ALL=C sort | tr -d "\r")
  if ! diff -u <(printf "%s\n" "$a") <(printf "%s\n" "$l") >/dev/null; then echo "[ATLAS] ap.tsv vs ledger differ"; fail=1; else echo "[ATLAS] ap.tsv == ledger"; fi
else echo "[ATLAS] skip (missing atlas or ledger)"; fi
dot -V >/dev/null 2>&1 || { echo "[PROOF] graphviz dot not found"; fail=1; }
if [ -f analysis/geom/proof.dot ]; then
  dot -Tsvg analysis/geom/proof.dot > analysis/geom/proof.svg
  [ -s analysis/geom/proof.svg ] && echo "[PROOF] svg rendered" || { echo "[PROOF] empty svg"; fail=1; }
else echo "[PROOF] skip (no proof.dot)"; fi
exit $fail
