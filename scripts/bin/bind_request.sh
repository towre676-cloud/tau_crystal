#!/usr/bin/env bash
set -Eeuo pipefail
set +H
umask 022

usage(){ echo "usage: bind_request.sh <stem> <file|-> [outdir=.tau_ledger]" >&2; exit 2; }
stem="${1:-}"; src="${2:-}"; outdir="${3:-receipts}"
[ -n "$stem" ] || usage
[ -n "$src" ]  || usage
mkdir -p "$outdir" analysis
d="$(scripts/bin/save_request_preimage.sh "$stem" "$src")"
printf "%s\n" "$d" > "$outdir/$stem.sha256"
[ -d ".tau_ledger" ] && printf "%s\n" "$d" > ".tau_ledger/$stem.sha256" || : 
printf "%s\n" "analysis/${stem}.request.canon.json" > "$outdir/$stem.preimage.path"
[ -d ".tau_ledger" ] && printf "%s\n" "analysis/${stem}.request.canon.json" > ".tau_ledger/$stem.preimage.path" || : 
printf "%s\n" "$d"
exit 0
