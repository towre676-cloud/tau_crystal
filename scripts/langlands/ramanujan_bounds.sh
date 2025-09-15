#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
. scripts/langlands/_bash_math.sh
src=".tau_ledger/langlands/ap_stable.json"; [ -s "$src" ] || src=".tau_ledger/langlands/ap.json"
[ -s "$src" ] || { echo "[skip] no ap*.json found"; exit 0; }
out="analysis/ramanujan.tsv"; : > "$out"; printf "%s\n" "p\tap\tbound\tok" >> "$out"
tr -d "\r" < "$src" | tr '[:upper:]' '[:lower:]' | sed "s/[{}]/\n/g" | awk '/p[[:space:]]*:/{p=$0; gsub(/.*p[[:space:]]*:[[:space:]]*/,"",p); gsub(/[^0-9]/,"",p)} /ap[[:space:]]*:/{a=$0; gsub(/.*ap[[:space:]]*:[[:space:]]*/,"",a); gsub(/[^0-9\.\-]/,"",a); if(p!=""){print p "\t" a; p=""; a=""}}' | while IFS=$t read -r P A; do
  [ -n "$P" ] || continue
  # scale ap to micro for integer compare
  Am=$(python - <<PY 2>/dev/null
try:
  import sys
  MICRO=1000000
  a=float(sys.argv[1]); print(int(round(a*MICRO)))
except Exception:
  print(0)
PY "$A")
  [ -z "$Am" ] && Am=0
  # 2*sqrt(p) scaled to micro
  rt=$(isqrt $((P)))  # integer sqrt floor
  Bm=$(( 2 * rt * MICRO ))
  ok="yes"
  if [ "${Am#-}" -gt "$Bm" ]; then ok="no"; fi
  printf %sn "$P	$A	$((Bm))	$ok" >> "$out"
done
