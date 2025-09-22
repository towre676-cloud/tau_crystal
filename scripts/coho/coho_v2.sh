#!/usr/bin/env bash
set +e; set +H; umask 022
. scripts/coho/lib_json.sh
SRC_JSON="${1:-.tau_ledger/last_run_A.json}"
DST_JSON="${2:-.tau_ledger/last_run_B.json}"
MAP_IN="${3:-.tau_ledger/morphism_pairs.tsv}"
TAU_TAB="${4:-.tau_ledger/per_leaf_tau.tsv}"
LAMBDA="${5:-0}"
mkdir -p .tau_ledger
SRC_LEAF=".tau_ledger/src_leaf.tsv"; DST_LEAF=".tau_ledger/dst_leaf.tsv"
scripts/coho/leaf_vector_from_receipt.sh "$SRC_JSON" "$SRC_LEAF" >/dev/null
scripts/coho/leaf_vector_from_receipt.sh "$DST_JSON" "$DST_LEAF" >/dev/null
MAP_TSV=".tau_ledger/morphism_map.tsv"; scripts/coho/build_morphism_map.sh "$SRC_LEAF" "$DST_LEAF" "$MAP_IN" > "$MAP_TSV"
DELTA_TSV=".tau_ledger/delta.tsv"; scripts/coho/delta_from_mapping.sh "$SRC_LEAF" "$DST_LEAF" "$MAP_TSV" > "$DELTA_TSV"
TAU_CERT=".tau_ledger/tau_cert.tsv"; [ -f "$TAU_TAB" ] || : > "$TAU_TAB"
scripts/coho/tau_cert_from_leaves.sh "$SRC_LEAF" "$DST_LEAF" "$TAU_TAB" "$LAMBDA" >/dev/null
SRC_ID=$(jstr "$SRC_JSON" id); DST_ID=$(jstr "$DST_JSON" id)
SRC_ENV=$(jstr "$SRC_JSON" env); DST_ENV=$(jstr "$DST_JSON" env)
SRC_ROOT=$(jstr "$SRC_JSON" root); DST_ROOT=$(jstr "$DST_JSON" root)
TS=$(date -u +%Y-%m-%dT%H:%M:%SZ)
OUT=".tau_ledger/coho_obstruction_v2.json"; : > "$OUT"
printf "{\n" >> "$OUT"
printf "  \\"cohomology_v2\\": {\n" >> "$OUT"
printf "    \\"timestamp\\": \\"%s\\",\n" "$TS" >> "$OUT"
printf "    \\"src\\": {\\"id\\": \\"%s\\", \\"env\\": \\"%s\\", \\"root\\": \\"%s\\"},\n" "$SRC_ID" "$SRC_ENV" "$SRC_ROOT" >> "$OUT"
printf "    \\"dst\\": {\\"id\\": \\"%s\\", \\"env\\": \\"%s\\", \\"root\\": \\"%s\\"},\n" "$DST_ID" "$DST_ENV" "$DST_ROOT" >> "$OUT"
printf "    \\"leaf_vector_src_tsv\\": \\"%s\\",\n" "$SRC_LEAF" >> "$OUT"
printf "    \\"leaf_vector_dst_tsv\\": \\"%s\\",\n" "$DST_LEAF" >> "$OUT"
printf "    \\"morphism_map_tsv\\": \\"%s\\",\n" "$MAP_TSV" >> "$OUT"
printf "    \\"delta_vector_tsv\\": \\"%s\\",\n" "$DELTA_TSV" >> "$OUT"
printf "    \\"tau_cert_tsv\\": \\"%s\\",\n" "$TAU_CERT" >> "$OUT"
printf "    \\"lambda_bound\\": %s\n" "$LAMBDA" >> "$OUT"
printf "  }\n}\n" >> "$OUT"
echo "$OUT"
