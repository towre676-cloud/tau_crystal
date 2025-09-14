#!/usr/bin/env bash
set -Eeuo pipefail; set +H
man="docs/manifest.md"; log=".tau_ledger/jupyter/trace.log"
[ -f "$log" ] || { echo "[err] $0: operation failed; check input and try again
sha=$(scripts/meta/_sha256.sh "$log")
tmp="docs/.manifest.jup.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## tau_trace (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp";; esac; done < "$man"
printf "%s\n" "## tau_trace (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "log: $log" >> "$tmp"
printf "%s\n" "sha256: $sha" >> "$tmp"
printf "%s\n" "" >> "$tmp"; mv "$tmp" "$man"
