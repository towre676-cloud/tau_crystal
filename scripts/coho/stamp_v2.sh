#!/usr/bin/env bash
set +e; set +H; umask 022
. scripts/coho/lib_json.sh
REC="corridor.receipt.tsv"; CHAIN=".tau_ledger/CHAIN"; touch "$REC" "$CHAIN"
J="$1"; [ -n "$J" ] || J=".tau_ledger/coho_obstruction_v2.json"
H=$(HASH "$J"); TS=$(date -u +%Y-%m-%dT%H:%M:%SZ); T="$(TAB)"
line="sha256:$H${T}$J"; grep -Fq "$line" "$REC" || printf "%s\n" "$line" >> "$REC"
cline="${TS}${T}coho_v2${T}sha256:${H}${T}${J}"; grep -Fq "$H" "$CHAIN" || printf "%s\n" "$cline" >> "$CHAIN"
