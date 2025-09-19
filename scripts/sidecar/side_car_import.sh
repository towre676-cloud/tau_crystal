#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
PACK="${1:-}"; [ -n "$PACK" ] && [ -f "$PACK" ] || { echo "[import] need pack path" >&2; exit 2; }
V="scripts/sidecar/side_car_verify.sh"
[ -x "$V" ] || { echo "[import] verifier missing: $V" >&2; exit 3; }
"$V" --strict "$PACK" >/dev/null
if command -v sha256sum >/dev/null 2>&1; then P=$(sha256sum "$PACK" | cut -d" " -f1); else P=$(shasum -a 256 "$PACK" | cut -d" " -f1); fi
TS=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
mkdir -p analysis
AT="analysis/atlas.jsonl"; touch "$AT"
printf "%s\n" "{\"type\":\"SIDECAR_IMPORT\",\"pack_sha256\":\"$P\",\"schema\":\"side-car-v1\",\"ts\":\"$TS\"}" >> "$AT"
echo "[import] OK: appended SIDECAR_IMPORT for $PACK"
