#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
src="${1:-.tau_ledger/langlands/ap_stable.json}"; [ -s "$src" ] || src=".tau_ledger/langlands/ap.json"
[ -s "$src" ] || { echo "[ramanujan] skip: no ap*.json"; exit 0; }
out="analysis/ramanujan.tsv"; : > "$out"; printf "%s\n" "p\tap\tbound_micro\tok" >> "$out"
tr -d "\r" < "$src" | tr '[:upper:]' '[:lower:]' | sed "s/[{}]/\n/g" | awk '/\"p\"[[:space:]]*:/{p=$0; sub(/^.*: */,"",p); gsub(/[^0-9]/,"",p)} /\"ap\"[[:space:]]*:/{a=$0; sub(/^.*: */,"",a); gsub(/[^0-9\.\-]/,"",a); if(p!=""){print p "\t" a; p=""; a=""}}' | while IFS=$t read -r P A; do
  [ -n "$P" ] || continue
  Am="$(dec_to_micro "$A")"
  rt="$(isqrt "$P")"
  Bm=$(( 2 * rt * MICRO ))
  ok="yes"; [ "${Am#-}" -gt "$Bm" ] && ok="no"
  printf %sn "$P	$A	$Bm	$ok" >> "$out"
done
echo "[ramanujan] wrote $out"
