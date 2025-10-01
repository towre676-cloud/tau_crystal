#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ID="${1:?motive id}"; KIND="${2:?Betti|deRham|comparison}"; LABEL="${3:?label}"; VALUE="${4:-0}"
DEST="analysis/motive/objects/$ID/periods"; mkdir -p "$DEST"
OUT="$DEST/${KIND}_${LABEL}.json"; : > "$OUT"
printf "{\n  \"motive\":\"%s\",\n  \"kind\":\"%s\",\n  \"label\":\"%s\",\n  \"value\":\"%s\"\n}\n" "$ID" "$KIND" "$LABEL" "$VALUE" >> "$OUT"
echo "[ok] period → $OUT"
