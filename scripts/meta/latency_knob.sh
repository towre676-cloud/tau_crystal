#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: LATENCY_MS=100 ./scripts/meta/latency_knob.sh
conf="analysis/latency_knob.env"; led=".tau_ledger/latency"; ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
mkdir -p "$(dirname "$conf")" "$led"
lat="${LATENCY_MS:-}"
if [ -z "$lat" ]; then echo "[latency] set LATENCY_MS"; exit 2; fi
printf "%s\n" "LATENCY_MS=$lat" > "$conf"
sig=$(printf "%s\n" "$lat|$ts" | sha256sum | awk "{print \$1}")
rec="$led/$ts.receipt.tsv"; : > "$rec"
printf "%s\t%s\n" "ts" "$ts" >> "$rec"
printf "%s\t%s\n" "latency_ms" "$lat" >> "$rec"
printf "%s\t%s\n" "config_sha256" "$(sha256sum "$conf" | awk "{print \$1}")" >> "$rec"
printf "%s\t%s\n" "knob_signature" "$sig" >> "$rec"
echo "[latency] knob set to $lat ms; receipt: $rec"
