#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ID="${1:?motive id}"; DEST="analysis/motive/objects/$ID/invariants"; mkdir -p "$DEST"
R="$DEST/regulator_stub.json"; : > "$R"
printf "{\n  \"motive\":\"%s\",\n  \"type\":\"BeilinsonRegulator\",\n  \"value\":\"0.0\",\n  \"status\":\"pending\"\n}\n" "$ID" >> "$R"
L="$DEST/L_function_stub.json"; : > "$L"
printf "{\n  \"motive\":\"%s\",\n  \"type\":\"MotivicLFunction\",\n  \"euler_factors\":[],\n  \"special_values\":[],\n  \"status\":\"pending\"\n}\n" "$ID" >> "$L"
echo "[ok] invariants → $DEST"
