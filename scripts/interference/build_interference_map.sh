#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C

a="${1:-}"
b="${2:-}"
window="${3:-20}"

if [ -z "${a}" ] || [ -z "${b}" ]; then
  echo "[err] usage: build_interference_map.sh <a.csv> <b.csv> [lag_window]"
  exit 2
fi
[ -f "$a" ] || { echo "[err] missing: $a"; exit 3; }
[ -f "$b" ] || { echo "[err] missing: $b"; exit 4; }

# minimal deps: awk + openssl must be present
command -v awk >/dev/null 2>&1 || { echo "[err] awk not found"; exit 5; }
command -v openssl >/dev/null 2>&1 || { echo "[err] openssl not found"; exit 6; }

shaA=$(openssl dgst -sha256 "$a" | awk '{print $2}')
shaB=$(openssl dgst -sha256 "$b" | awk '{print $2}')
ts="$(date -u +%FT%TZ)"

mkdir -p analysis/interference .tau_ledger/interference
lagcsv="analysis/interference/interference_${ts//:/-}.csv"
: > "$lagcsv"; printf '%s\n' "lag,score" >> "$lagcsv"

best_lag=0
best_score="-2"

# tmp awk file (fallback if mktemp missing)
tmpawk="$(mktemp -p . .tmp.im_awk.XXXXXX 2>/dev/null || echo .tmp.im_awk.$$)"
: > "$tmpawk"
{
  echo 'BEGIN{FS=","}'
  echo 'FNR==1 && ($1 ~ /^[tT]$/ || $1 ~ /time/){next}'
  echo '{gsub(/\r/,"")}'
  echo 'FNR==NR{ if($1!=""){ A[$1]=$2 } next }'
  echo '{ if($1!=""){ B[$1]=$2 } }'
  echo 'END{'
  echo '  cnt=0; sx=0; sy=0; sxx=0; syy=0; sxy=0;'
  echo '  for(t in A){ t2=t+L; if(t2 in B){'
  echo '    x=A[t]+0; y=B[t2]+0;'
  echo '    sx+=x; sy+=y; sxx+=x*x; syy+=y*y; sxy+=x*y; cnt++'
  echo '  }}'
  echo '  if(cnt<2){ print "NA"; exit }'
  echo '  mx=sx/cnt; my=sy/cnt;'
  echo '  vx=sxx/cnt - mx*mx; vy=syy/cnt - my*my;'
  echo '  if(vx<=0 || vy<=0){ print "NA"; exit }'
  echo '  r=(sxy/cnt - mx*my)/sqrt(vx*vy);'
  echo '  printf("%.6f", r)'
  echo '}'
} >> "$tmpawk"

# portable lag loop
L=$((-window))
while [ "$L" -le "$window" ]; do
  s="$(awk -v L="$L" -f "$tmpawk" "$a" "$b" 2>/dev/null || echo NA)"
  if [ "$s" != "NA" ]; then
    printf '%s\n' "$L,$s" >> "$lagcsv"
    awk "BEGIN{exit !($s>$best_score)}" && { best_score="$s"; best_lag="$L"; } || true
  fi
  L=$((L+1))
done

rm -f "$tmpawk"

sumjson=".tau_ledger/interference/${ts//:/-}_summary.json"
: > "$sumjson"
printf '%s' "{" >> "$sumjson"
printf '%s' "\"ts\":\"$ts\"," >> "$sumjson"
printf '%s' "\"input_a\":\"$(printf '%s' "$a" | sed 's/\"/'\''/g')\"," >> "$sumjson"
printf '%s' "\"sha256_a\":\"$shaA\"," >> "$sumjson"
printf '%s' "\"input_b\":\"$(printf '%s' "$b" | sed 's/\"/'\''/g')\"," >> "$sumjson"
printf '%s' "\"sha256_b\":\"$shaB\"," >> "$sumjson"
printf '%s' "\"lag_window\":$window," >> "$sumjson"
printf '%s' "\"best_lag\":$best_lag," >> "$sumjson"
printf '%s' "\"best_score\":$best_score," >> "$sumjson"
printf '%s' "\"csv\":\"$lagcsv\"}" >> "$sumjson"

echo "[ok] interference → $lagcsv ; summary → $sumjson"
