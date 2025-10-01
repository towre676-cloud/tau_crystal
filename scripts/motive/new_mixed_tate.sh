#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ID="${1:-MTM_affine_rg}"
MU0="${2:-1.0000000000}"
BPARM="${3:-0.1234567890}"
DEST="analysis/motive/objects/$ID"; mkdir -p "$DEST"/{periods,comparisons,invariants}
PARAMS="$DEST/params.json"; : > "$PARAMS"
printf "{\n  \"mu0\":\"%s\",\n  \"b\":\"%s\",\n  \"rg\":\"affine_one_loop\"\n}\n" "$MU0" "$BPARM" >> "$PARAMS"
WEIGHTS="__ARR__[0,1,2]"
COMP="__RAW__{\"periods\":\"periods/\",\"comparisons\":\"comparisons/\",\"invariants\":\"invariants/\"}"
"scripts/motive/_json_obj.sh" "$DEST/motive.json" id "$ID" base_field "Q(mu0,b)" type "mixed_tate" weights "$WEIGHTS" params "__RAW__$(cat "$PARAMS")" weyl_group "B5" components "$COMP"
echo "[ok] motive → $DEST/motive.json"
