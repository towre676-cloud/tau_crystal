#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
stem="${1:?usage: write_request_note.sh <stem> <digest> [preimage_path]}"
digest="${2:?usage: write_request_note.sh <stem> <digest> [preimage_path] }"
pre="${3:-analysis/${stem}.request.canon.json}"
outdir="receipts"; mkdir -p "$outdir"
out="$outdir/${stem}.request.note.json"
: > "$out"
printf "%s" "{" >> "$out"
printf "%s" "\"digest\":\"$digest\"" >> "$out"
printf "%s" ",\"preimage\":\"$pre\"" >> "$out"
printf "%s\n" "}" >> "$out"
printf "%s\n" "$out"
