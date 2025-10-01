#!/usr/bin/env bash
set -euo pipefail; set +H
IN="$1"; OUT="$2"; ext="${IN##*.}"; ext="${ext,,}"
case "$ext" in
  csv) awk -F"," '{printf("%s\t%s\t%s\n",$1,$2,$3)}' "$IN" ;;
  tsv|txt) awk '{gsub(/[ ,]+/,"\t"); print $0}' "$IN" ;;
  pts) awk '/\{/{inb=1; next} /\}/{inb=0} inb{print}' "$IN" | awk '{if(NF==2) printf("%s\t%s\t0\n",$1,$2); else printf("%s\t%s\t%s\n",$1,$2,$3)}' ;;
  *) echo "Unsupported ext: ${ext}" >&2; exit 6 ;;
esac |
awk -F"\t" 'NF>=2 && $1!~ /^#/ {if(NF==2) printf("%s\t%s\t0\n",$1,$2); else printf("%s\t%s\t%s\n",$1,$2,$3)}' > "$OUT.tmp"
lines=$(wc -l < "$OUT.tmp" | tr -d " ")
[ "$lines" -eq 68 ] || { rm -f "$OUT.tmp"; exit 7; }
mv "$OUT.tmp" "$OUT"; echo "$OUT"
