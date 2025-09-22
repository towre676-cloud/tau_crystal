#!/usr/bin/env bash
set -euo pipefail; set +H
# Usage: gen_eta_pentagonal.sh [MAX_N]  (default 200)
MAX_N="${1:-200}"
case "$MAX_N" in (*[!0-9]*|"") echo "MAX_N must be integer"; exit 2;; esac
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
DATA="$ROOT/ramanujan/data"
mkdir -p "$DATA"

# ---- Compute right-hand side (R) via generalized pentagonal numbers ----
declare -a R P KVAL SIGN
for ((i=0;i<=MAX_N;i++)); do R[i]=0; P[i]=0; KVAL[i]=""; SIGN[i]=0; done

# we need k such that n = k(3k-1)/2 or k(3k+1)/2 <= MAX_N
# bound on |k|: solve k(3k-1)/2 <= MAX_N -> k ~ sqrt(2*MAX_N/3) + 1
kmax=$(( ( ( (MAX_N*2)/3 ) + 2 )))
if [ $kmax -lt 10 ]; then kmax=10; fi
for ((k=-kmax; k<=kmax; k++)); do
  # n1 = k(3k-1)/2
  n1=$(( (k*(3*k-1))/2 ))
  if [ "$n1" -ge 0 ] && [ "$n1" -le "$MAX_N" ]; then
    s=$(( (k%2==0) ? 1 : -1 ))
    R[n1]=$(( R[n1] + s ))
    P[n1]=1; KVAL[n1]="$k"; SIGN[n1]="$s"
  fi
  # n2 = k(3k+1)/2
  n2=$(( (k*(3*k+1))/2 ))
  if [ "$n2" -ge 0 ] && [ "$n2" -le "$MAX_N" ]; then
    s=$(( (k%2==0) ? 1 : -1 ))
    R[n2]=$(( R[n2] + s ))
    P[n2]=1; KVAL[n2]="$k"; SIGN[n2]="$s"
  fi
done

# ---- Compute left-hand side (L) as coefficients of product ∏_{m>=1}(1-q^m) up to MAX_N ----
declare -a L
for ((i=0;i<=MAX_N;i++)); do L[i]=0; done
L[0]=1
# Classic dynamic programming: for each m, multiply by (1 - q^m) -> L[n] = L[n] - L[n-m]
for ((m=1; m<=MAX_N; m++)); do
  for ((n=MAX_N; n>=m; n--)); do
    L[n]=$(( L[n] - L[n-m] ))
  done
done

# ---- Emit audit table: eta_pentagonal.tsv (n, L, R, is_pentagonal, k, sign) ----
AUD="$DATA/eta_pentagonal.tsv"
rm -f "$AUD"
for ((n=0; n<=MAX_N; n++)); do
  ip="${P[n]}"
  kv="${KVAL[n]}"
  sg="${SIGN[n]}"
  if [ "$ip" -eq 0 ]; then kv=""; sg=0; fi
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$n" "${L[n]}" "${R[n]}" "$ip" "$kv" "$sg"
done > "$AUD"
echo "wrote $AUD (0..$MAX_N)"

# ---- Emit verifier inputs (n>=1): eta_left.tsv, eta_right.tsv ----
EL="$DATA/eta_left.tsv"; ER="$DATA/eta_right.tsv"
rm -f "$EL" "$ER"
for ((n=1; n<=MAX_N; n++)); do
  printf "%s\t%s\n" "$n" "${L[n]}" >> "$EL"
  printf "%s\t%s\n" "$n" "${R[n]}" >> "$ER"
done
echo "wrote $EL and $ER (1..$MAX_N)"

# ---- Quick consistency check: L vs R full range ----
fail=0
for ((n=0; n<=MAX_N; n++)); do
  if [ "${L[n]}" -ne "${R[n]}" ]; then echo "mismatch at n=" "$n" ": L=" "${L[n]}" " R=" "${R[n]}"; fail=1; break; fi
done
if [ "$fail" -eq 0 ]; then echo "local check: L == R for 0..$MAX_N"; fi
