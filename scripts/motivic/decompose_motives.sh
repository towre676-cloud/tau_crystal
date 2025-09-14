#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
seqfile="${1:-.tau_ledger/seq/tau.csv}"; out=".tau_ledger/langlands/motives.json"
mkdir -p ".tau_ledger/langlands"
[ -s "$seqfile" ] || { echo "{\"status\":\"no_tau\",\"motives\":[]}" > "$out"; echo "$out"; exit 0; }
tmp="$(mktemp)"; awk -F, "NR>1{print \$2}" "$seqfile" > "$tmp"; N=$(wc -l < "$tmp" | awk "{print \$1}")
[ "${N:-0}" -ge 12 ] || { echo "{\"status\":\"short\",\"motives\":[]}" > "$out"; rm -f "$tmp"; echo "$out"; exit 0; }
turns="$(mktemp)"; : > "$turns"; prev=""; i=0
while read -r v; do i=$((i+1)); if [ -n "$prev" ]; then s=$(awk -v a="$prev" -v b="$v" "BEGIN{print b-a}"); dir="flat";
  if awk "BEGIN{exit !('s>0')}" ; then dir="up"; elif awk "BEGIN{exit !('s<0')}" ; then dir="down"; fi;
  echo "$i $dir" >> "$turns"; fi; prev="$v"; done < "$tmp"
segs="$(mktemp)"; : > "$segs"; last=1; lastd=""
while read -r idx d; do if [ -z "$lastd" ]; then lastd="$d"; continue; fi; if [ "$d" != "$lastd" ] && [ "$d" != "flat" ]; then echo "$last $idx" >> "$segs"; last="$idx"; lastd="$d"; fi; done < "$turns"; echo "$last $N" >> "$segs"
W=$((N/6)); [ "$W" -lt 4 ] && W=4; first=1; echo "{" > "$out"; echo -n "\"status\":\"ok\",\"motives\":[" >> "$out"
while read -r a b; do len=$((b-a+1)); [ "$len" -lt "$W" ] && continue; mu=$(awk -v s="$a" -v e="$b" "NR>=s && NR<=e{c++; S+=\$1} END{if(c==0)print 0; else print S/c}" "$tmp");
  var=$(awk -v s="$a" -v e="$b" "NR>=s && NR<=e{c++; S+=\$1; Q+=\$1*\$1} END{if(c==0)print 0; else{m=S/c; print Q/c - m*m}}" "$tmp");
  [ $first -eq 1 ] && first=0 || echo -n "," >> "$out"; echo -n "{\"start\":$a,\"end\":$b,\"len\":$len,\"mean\":$mu,\"var\":$var}" >> "$out"
done < "$segs"; echo "]}" >> "$out"; rm -f "$tmp" "$turns" "$segs"; echo "$out"
