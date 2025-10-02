#!/usr/bin/env bash
set +H
umask 022
OUTDIR="validation/input"
mkdir -p "$OUTDIR"
i=1
while [ $i -le ${1:-5} ]; do
  F=$(printf "%s/face_%02d.tsv" "$OUTDIR" "$i")
  : > "$F"
  j=0
  while [ $j -lt 68 ]; do
    # deterministic pseudo-geometry: x=j/100, y=i/10, z=(i+j)%7 / 50
    X=$(printf "%.2f" "$(awk "BEGIN{print $j/100}")")
    Y=$(printf "%.2f" "$(awk "BEGIN{print $i/10}")")
    MOD=$(( (i + j) % 7 ))
    Z=$(printf "%.2f" "$(awk "BEGIN{print $MOD/50}")")
    printf "%s\t%s\t%s\n" "$X" "$Y" "$Z" >> "$F"
    j=$((j+1))
  done
  i=$((i+1))
done
echo "minted $(ls -1 "$OUTDIR"/face_*.tsv 2>/dev/null | wc -l) synthetic TSVs in $OUTDIR"
