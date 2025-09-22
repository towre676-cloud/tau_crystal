#!/usr/bin/env bash
set -euo pipefail; set +H
MAX_N="${1:-300}"
case "$MAX_N" in (*[!0-9]*|"") echo "usage: $0 [MAX_N]"; exit 2;; esac
DATA="ramanujan/data"; mkdir -p "$DATA"
EL="$DATA/eta_left.tsv"; ER="$DATA/eta_right.tsv"; AUD="$DATA/eta_pentagonal.tsv"
rm -f "$EL" "$ER" "$AUD"
# ---- RHS: generalized pentagonal numbers (k>=0; add each exponent once)
declare -a R P K S; for((i=0;i<=MAX_N;i++));do R[i]=0; P[i]=0; K[i]=""; S[i]=0; done
kmax=$(( ( (MAX_N*2)/3 ) + 4 ))
for((k=0;k<=kmax;k++));do
  s=$(( (k%2==0) ? 1 : -1 ))
  if [ "$k" -eq 0 ]; then
    # only one term at n=0
    R[0]=$(( R[0]+1 )); P[0]=1; K[0]=0; S[0]=1; continue
  fi
  n1=$(( (k*(3*k-1))/2 ))
  n2=$(( (k*(3*k+1))/2 ))
  if [ "$n1" -le "$MAX_N" ]; then R[n1]=$(( R[n1]+s )); P[n1]=1; K[n1]="$k"; S[n1]="$s"; fi
  if [ "$n2" -le "$MAX_N" ]; then R[n2]=$(( R[n2]+s )); P[n2]=1; K[n2]="$k"; S[n2]="$s"; fi
done
# ---- LHS: coefficients of ∏(1 - q^m) via DP
declare -a L; for((i=0;i<=MAX_N;i++));do L[i]=0; done; L[0]=1
for((m=1;m<=MAX_N;m++));do for((n=MAX_N;n>=m;n--));do L[n]=$(( L[n]-L[n-m] )); done; done
# ---- Emit audit (n, L, R, is_pentagonal, k, sign)
for((n=0;n<=MAX_N;n++));do ip="${P[n]}"; kv="${K[n]}"; sg="${S[n]}"; [ "$ip" -eq 0 ] && { kv=""; sg=0; }; printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$n" "${L[n]}" "${R[n]}" "$ip" "$kv" "$sg"; done > "$AUD"
printf "%s\n" "# n\tcoeff" > "$EL"; for((n=1;n<=MAX_N;n++));do printf "%s\t%s\n" "$n" "${L[n]}"; done >> "$EL"
printf "%s\n" "# n\tcoeff" > "$ER"; for((n=1;n<=MAX_N;n++));do printf "%s\t%s\n" "$n" "${R[n]}"; done >> "$ER"
# ---- Local sanity
for((n=0;n<=MAX_N;n++));do [ "${L[n]}" -ne "${R[n]}" ] && { echo "mismatch at n=$n"; exit 1; }; done
echo "wrote $AUD, $EL, $ER (0..$MAX_N) and L==R locally"
