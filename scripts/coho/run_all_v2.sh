#!/usr/bin/env bash
set +e; set +H; umask 022
. scripts/coho/lib_json.sh
SRC="${1:-.tau_ledger/last_run_A.json}"
DST="${2:-.tau_ledger/last_run_B.json}"
MAP="${3:-.tau_ledger/morphism_pairs.tsv}"
TAU="${4:-.tau_ledger/per_leaf_tau.tsv}"
LBD="${5:-0}"
OUT=$(scripts/coho/coho_v2.sh "$SRC" "$DST" "$MAP" "$TAU" "$LBD")
scripts/coho/stamp_v2.sh "$OUT"
git add "$OUT" .tau_ledger/src_leaf.tsv .tau_ledger/dst_leaf.tsv .tau_ledger/morphism_map.tsv .tau_ledger/delta.tsv .tau_ledger/tau_cert.tsv corridor.receipt.tsv .tau_ledger/CHAIN 2>/dev/null || : 
git commit -m "coho-v2: group-valued leaf obstruction + tau Lipschitz cert + corridor/CHAIN stamp" 2>/dev/null || : 
git push origin main 2>/dev/null || : 
echo "coho v2 complete: $OUT"
scripts/coho/report_v2.sh >/dev/null || : 
git add .tau_ledger/delta_report.md 2>/dev/null || : 
