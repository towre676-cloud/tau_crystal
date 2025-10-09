#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e
out="receipts/_scratch/touched_$(date +%Y%m%d_%H%M%S).json"
printf "%s\n" "{" > "$out"
printf "%s\n" "  \"ok\": true," >> "$out"
printf "%s\n" "  \"ts\": \"$(date -u +"%Y-%m-%dT%H:%M:%SZ")\"" >> "$out"
printf "%s\n" "}" >> "$out"
printf "%s\n" "$out"
