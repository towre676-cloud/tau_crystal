#!/usr/bin/env bash
set -Eeuo pipefail; set +H
. scripts/langlands/_bash_math.sh
extract_series(){
  # prints micro-int values, normalized by max per-file to [0..MICRO]
  f="${1:?}"; tmp=$(tr -cs "0-9.\n" "\n" < "$f" | sed -e "/^$/d")
  # find max (as micro)
  max=0; while IFS= read -r v; do m=$(dec_to_micro "$v"); [ "$m" -gt "$max" ] && max=$m; done <<< "$tmp"
  [ "$max" -eq 0 ] && return 0
  while IFS= read -r v; do m=$(dec_to_micro "$v"); n=$(( (m*MICRO)/max )); n=$(micro_clamp01 "$n"); echo "$n"; done <<< "$tmp"
}
hecke_smooth_val(){
  # y = (x + sqrt(x*MICRO)) / 2 in micro space
  x=$(( ${1:-0} )); s=$(isqrt $(( x*MICRO ))); echo $(( (x + s)/2 ))
}
theta_val(){
  x=$(( ${1:-0} )); S=$(( ${2:-MICRO} )); T=$(( ${3:-0} ));
  y=$(( (S*x)/MICRO + T )); micro_clamp01 "$y"
}
dir_signature(){
  # mean of values after optional smoothing/lift; mode: raw|hecke|theta S T
  mode="${1:-raw}"; root="${2:-.tau_ledger}"; S="${3:-}"; T="${4:-}"
  sum=0; n=0
  while IFS= read -r -d "" f; do
    while IFS= read -r x; do
      case "$mode" in
        raw)   y="$x";;
        hecke) y=$(hecke_smooth_val "$x");;
        theta) y=$(theta_val "$x" "$S" "$T");;
      esac
      sum=$((sum + y)); n=$((n+1))
    done < <(extract_series "$f")
  done < <(find "$root" -type f -name "*.json" -print0 2>/dev/null)
  if [ "$n" -eq 0 ]; then echo "0 0"; else printf "%d %d\n" "$sum" "$n"; fi
}
mean_micro(){ sum=$(( ${1:-0} )); n=$(( ${2:-1} )); [ "$n" -eq 0 ] && echo 0 || echo $(( sum / n )); }
modular_check(){
  # usage: modular_check <dirA> <dirB> <tol_micro>
  A="${1:?}"; B="${2:?}"; tol=$(( ${3:-1000} ))
  read sA nA < <(dir_signature hecke "$A")
  read sB nB < <(dir_signature hecke "$B")
  mA=$(mean_micro "$sA" "$nA"); mB=$(mean_micro "$sB" "$nB");
  diff=$(( mA>mB ? mA-mB : mB-mA ))
  printf "diff_micro=%d\tmA=%d\tmB=%d\tnA=%d\tnB=%d\n" "$diff" "$mA" "$mB" "$nA" "$nB"
  [ "$diff" -le "$tol" ]
}
theta_scan(){
  # sweep S in {0.70..1.00 step .05}, T in {0..50000 step 10000} micro-units
  A="${1:?}"; B="${2:?}"; out="${3:-analysis/bash_theta_scan.tsv}"
  mkdir -p "$(dirname "$out")"; : > "$out"; printf "%s\n" "S_micro\tT_micro\tdiff\tmA\tmB\tnA\tnB" >> "$out"
  read sA nA < <(dir_signature hecke "$A"); mA=$(mean_micro "$sA" "$nA")
  for S in 700000 750000 800000 850000 900000 950000 1000000; do
    for T in 0 10000 20000 30000 40000 50000; do
      read sB nB < <(dir_signature theta "$B" "$S" "$T"); mB=$(mean_micro "$sB" "$nB")
      d=$(( mA>mB ? mA-mB : mB-mA ))
      printf "%d\t%d\t%d\t%d\t%d\t%d\t%d\n" "$S" "$T" "$d" "$mA" "$mB" "$nA" "$nB" >> "$out"
    done
  done
  echo "$out"
}
