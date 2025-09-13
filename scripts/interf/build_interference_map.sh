#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
outdir=".tau_ledger/interf"; mkdir -p "$outdir"
svg="$outdir/interference.svg"; tmp="$outdir/rows.tmp"; : > "$tmp"
sources=(CHAIN timefolds entropy signature holography federation)
hashrow() {
  x="$1"; [ -f "$x" ] || { echo ""; return; }
  cksum < "$x" | cut -d" " -f1 | tr -dc "0-9" | fold -w60 | head -n 1
}
for src in "${sources[@]}"; do
  row=""
  case "$src" in
    CHAIN) row=$(hashrow .tau_ledger/CHAIN) ;;
    timefolds) for f in .tau_ledger/timefolds/*.meta; do [ -f "$f" ] && row="${row}$(hashrow "$f")"; done ;;
    entropy) f=$(ls -1 .tau_ledger/entropy/*.json 2>/dev/null | tail -1); row=$(hashrow "$f") ;;
    signature) f=$(ls -1 .tau_ledger/signature/*.sig 2>/dev/null | tail -1); row=$(hashrow "$f") ;;
    holography) f=$(ls -1 .tau_ledger/holo/*.json 2>/dev/null | tail -1); row=$(hashrow "$f") ;;
    federation) f=$(ls -1 .tau_ledger/xref/index.v1 2>/dev/null); row=$(hashrow "$f") ;;
  esac
  echo "$row" >> "$tmp"
done
rows=$(cat "$tmp" | wc -l)
cols=60
px() { v="$1"; c=$(( v % 255 )); printf "#%02x%02x%02x" "$c" "$((c/2))" "$((255-c))"; }
: > "$svg"
printf "%s\n" "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"$cols\" height=\"$rows\" shape-rendering=\"crispEdges\">" >> "$svg"
y=0; while IFS= read -r line; do
  x=0; while [ "$x" -lt "$cols" ]; do
