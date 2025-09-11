#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
kind="${1:-warm}"
out=".tau_ledger/bench/runs.ndjson"
mkdir -p "$(dirname "$out")"
ts="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
osname="$(uname -s 2>/dev/null || echo unknown)"
runner="$([ "${GITHUB_ACTIONS:-false}" = "true" ] && echo github || echo local)"
if [ "$kind" = "cold" ]; then rm -rf .lake 2>/dev/null || true; fi
SECONDS=0
if command -v lake >/dev/null 2>&1; then lake build >/dev/null 2>&1 || true; else sleep 1; fi
secs="$SECONDS"
tmp=".tau_ledger/bench/.tmp.$$"
: > "$tmp"
printf "{\n" >> "$tmp"
printf "\"timestamp\":\"%s\",\n" "$ts" >> "$tmp"
printf "\"os\":\"%s\",\n" "$osname" >> "$tmp"
printf "\"runner\":\"%s\",\n" "$runner" >> "$tmp"
printf "\"type\":\"%s\",\n" "$kind" >> "$tmp"
printf "\"seconds\":%s\n" "$secs" >> "$tmp"
printf "}\n" >> "$tmp"
tr -d "\n" < "$tmp" >> "$out"; printf "\n" >> "$out"
rm -f "$tmp"
printf "%s\n" "[bench] $osname $runner ${secs}s -> $kind" >&2
