#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
IN="${1:-analysis/bash_theta_scan.tsv}"
OUT="analysis/morse_crit.tsv"

[ -s "$IN" ] || { echo "[morse2d] no scan data: $IN"; exit 0; }

declare -A D Sset Tset
# read TSV (skip header, ensure numeric)
first=1
while IFS=$'\t' read -r S T diff mA mB nA nB; do
  if [ "$first" = 1 ]; then first=0; case "$S" in ''|*[!0-9-]* ) continue;; esac; fi
  case "$S$T$diff" in *[!0-9-]* ) continue;; esac
  key="$S,$T"
  D["$key"]="$diff"
  Sset["$S"]=1
  Tset["$T"]=1
done < "$IN"

# get minimal positive steps
readarray -t Svals < <(printf '%s\n' "${!Sset[@]}" | sort -n)
readarray -t Tvals < <(printf '%s\n' "${!Tset[@]}" | sort -n)
stepS=0; for ((i=1;i<${#Svals[@]};i++)); do d=$(( Svals[i]-Svals[i-1] )); (( d>0 && (stepS==0 || d<stepS) )) && stepS=$d; done
stepT=0; for ((i=1;i<${#Tvals[@]};i++)); do d=$(( Tvals[i]-Tvals[i-1] )); (( d>0 && (stepT==0 || d<stepT) )) && stepT=$d; done
: > "$OUT"; printf "%s\t%s\t%s\t%s\t%s\n" "S_micro" "T_micro" "type" "Delta" "Hess_det" >> "$OUT"
(( stepS==0 || stepT==0 )) && { echo "[morse2d] degenerate grid (stepS=$stepS stepT=$stepT); wrote header"; exit 0; }

minima=0
for key in "${!D[@]}"; do
  s="${key%,*}"; t="${key#*,}"; d="${D[$key]}"
  any=0; less=0
  for dx in -1 0 1; do
    for dy in -1 0 1; do
      [[ $dx == 0 && $dy == 0 ]] && continue
      ss=$(( s + dx*stepS )); tt=$(( t + dy*stepT ))
      nkey="$ss,$tt"
      if [[ -n "${D[$nkey]+_}" ]]; then
        any=1
        nd="${D[$nkey]}"
        (( nd < d )) && less=1
      fi
    done
  done
  if (( any==1 && less==0 )); then
    # crude discrete 2nd derivatives (if neighbors exist)
    fx2=0; fy2=0
    k1="$((s-stepS)),$t"; k2="$((s+stepS)),$t"
    [[ -n "${D[$k1]+_}" && -n "${D[$k2]+_}" ]] && fx2=$(( D[$k1] + D[$k2] - 2*d ))
    k3="$s,$((t-stepT))"; k4="$s,$((t+stepT))"
    [[ -n "${D[$k3]+_}" && -n "${D[$k4]+_}" ]] && fy2=$(( D[$k3] + D[$k4] - 2*d ))
    printf "%s\t%s\t%s\t%s\t%s\n" "$s" "$t" "minimum" "$d" "$((fx2*fy2))" >> "$OUT"
    (( minima++ ))
  fi
done

echo "[morse2d] minima=$minima -> $OUT"
