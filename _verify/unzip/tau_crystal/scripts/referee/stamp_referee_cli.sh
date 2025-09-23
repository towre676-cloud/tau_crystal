#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
BIN="${1:-}"; [ -n "$BIN" ] && [ -f "$BIN" ] || { echo "[referee] need CLI path" >&2; exit 2; }
if command -v sha256sum >/dev/null 2>&1; then H=$(sha256sum "$BIN" | cut -d" " -f1); else H=$(shasum -a 256 "$BIN" | cut -d" " -f1); fi
TS=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
AT="analysis/atlas.jsonl"; mkdir -p analysis; touch "$AT"
printf "%s\n" "{\"type\":\"REFEREE_CLI\",\"bin_hash\":\"$H\",\"ts\":\"$TS\"}" >> "$AT"
echo "[referee] stamped REFEREE_CLI ($H)"
