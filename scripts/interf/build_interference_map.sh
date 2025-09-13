#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
outdir=".tau_ledger/interf"; svg="$outdir/interference.svg"; rows_file="$outdir/rows.txt"
mkdir -p "$outdir"; : > "$rows_file"
hex60() { f="$1"; [ -f "$f" ] || { echo ""; return; }; scripts/meta/_sha256.sh "$f" | cut -c1-60; }
row_from_glob() { g="$1"; last=$(ls -1 $g 2>/dev/null | LC_ALL=C sort | tail -n 1 || true); [ -n "$last" ] && hex60 "$last" || echo ""; }
echo "$(hex60 .tau_ledger/CHAIN)" >> "$rows_file"
r=""; for m in .tau_ledger/timefolds/*.meta; do [ -f "$m" ] || continue; r="$r$(hex60 "$m")"; done; echo "$r" >> "$rows_file"
echo "$(row_from_glob ".tau_ledger/entropy/*.json")"    >> "$rows_file"
echo "$(row_from_glob ".tau_ledger/signature/*.sig")"  >> "$rows_file"
echo "$(row_from_glob ".tau_ledger/holo/*.json")"      >> "$rows_file"
echo "$(row_from_glob ".tau_ledger/xref/index.v1")"    >> "$rows_file"
rows=$(wc -l < "$rows_file" | tr -d " ")
cols=60
: > "$svg"
printf "%s\n" "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"$cols\" height=\"$rows\" shape-rendering=\"crispEdges\">" >> "$svg"
y=0
while IFS= read -r line; do
  [ -n "$line" ] || { y=$((y+1)); continue; }
  x=1; while [ "$x" -le "$cols" ]; do
    ch=$(printf "%s" "$line" | cut -c"$x")
    case "$ch" in
      [0-9]) v=$(( 10#$ch )) ;;
      a) v=10 ;; b) v=11 ;; c) v=12 ;; d) v=13 ;; e) v=14 ;; f) v=15 ;;
      *) v=0 ;;
    esac
    r=$(( v*16 )); g=$(( v*8 )); b=$(( 255 - v*16 ))
    printf "<rect x=\\"%s\\" y=\\"%s\\" width=\\"1\\" height=\\"1\\" fill=\\"#%02x%02x%02x\\"/>\\n" $((x-1)) "$y" "$r" "$g" "$b" >> "$svg"
    x=$((x+1))
  done
  y=$((y+1))
done < "$rows_file"
printf "%s\n" "</svg>" >> "$svg"
