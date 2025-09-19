#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

CURVE="11a1"; N=11
P_MAX="${P_MAX:-199}"   # primes up to this bound
M_MAX="${M_MAX:-512}"   # q-expansion terms (n ≤ M_MAX)
OUTP="analysis/hecke_11a1.tsv"
OUTQ="analysis/qexp_11a1.tsv"
OUTL="analysis/L_11a1.tsv"
OUTJ="analysis/hecke_11a1_receipt.json"

ap_cmd="scripts/math/curve_11a1.sh"
[ -x "$ap_cmd" ] || { echo "[hecke:11a1] missing $ap_cmd" >&2; exit 2; }

is_prime(){ scripts/math/curve_11a1.sh prime "$1"; }

# 2.1 collect a_p and check Hasse bound
: > "$OUTP"
printf "p\ta_p\tbound_ok\n" >> "$OUTP"
p=2
while [ "$p" -le "$P_MAX" ]; do
  if [ "$(is_prime "$p")" = 1 ] && [ $((p%N)) -ne 0 ] && [ "$p" -ne 2 ]; then
    ap="$("$ap_cmd" ap "$p")"
    if [ "$ap" != "NA" ]; then
      # Hasse (Ramanujan for weight 2): |a_p| ≤ 2√p
      ok=$(awk -v a="$ap" -v p="$p" 'BEGIN{ if(a<0) a=-a; bound=2*sqrt(p); print (a<=bound+1e-12)?"1":"0"}')
      printf "%d\t%d\t%s\n" "$p" "$ap" "$ok" >> "$OUTP"
    fi
  fi
  if [ "$p" -eq 2 ]; then p=3; else p=$((p+2)); fi
done

# 2.2 build a_n up to M_MAX via multiplicativity + Hecke recursion
# cache a_p^k in assoc arrays (bash + awk hybrid kept simple)
# write q-expansion leaf as TSV: n  a_n
: > "$OUTQ"
printf "n\ta_n\n" >> "$OUTQ"

# Parse a_p into arrays
mapfile -t APS < <(awk 'NR>1{print $1":"$2}' "$OUTP")
declare -A a_p
for kv in "${APS[@]}"; do p="${kv%%:*}"; val="${kv#*:}"; a_p["$p"]="$val"; done

declare -A a_pk   # key "p^k" -> value
a_pk_key(){ echo "$1^$2"; }

a_pk_get(){
  local p=$1 k=$2; local key; key=$(a_pk_key "$p" "$k")
  if [[ ${a_pk[$key]+_} ]]; then echo "${a_pk[$key]}"; return; fi
  if [ "$k" -eq 0 ]; then a_pk[$key]=1; echo 1; return; fi
  if [ "$k" -eq 1 ]; then a_pk[$key]="${a_p[$p]}"; echo "${a_p[$p]}"; return; fi
  # recursion: a_{p^k} = a_p a_{p^{k-1}} - p a_{p^{k-2}}
  local ak1 ak2
  ak1=$(a_pk_get "$p" $((k-1)))
  ak2=$(a_pk_get "$p" $((k-2)))
  local val=$(( a_p[$p]*ak1 - p*ak2 ))
  a_pk[$key]="$val"; echo "$val"
}

# factor n, multiplicative assembly
factor_small(){
  local n=$1
  local f="" e
  local d=2
  while [ $((d*d)) -le "$n" ]; do
    e=0
    while [ $((n%d)) -eq 0 ]; do n=$((n/d)); e=$((e+1)); done
    [ "$e" -gt 0 ] && f+="$d^$e "
    d=$((d+1))
  done
  [ "$n" -gt 1 ] && f+="$n^1"
  echo "$f"
}

a_n(){
  local n=$1
  [ "$n" -eq 1 ] && { echo 1; return; }
  local fac; fac="$(factor_small "$n")"
  local prod=1
  for term in $fac; do
    local p=${term%%^*} k=${term#*^}
    # unknown prime factor beyond our a_p table → best effort (stop early)
    if [[ -z "${a_p[$p]+_}" ]]; then echo ""; return; fi
    local apk; apk=$(a_pk_get "$p" "$k")
    prod=$(( prod * apk ))
  done
  echo "$prod"
}

n=1
while [ "$n" -le "$M_MAX" ]; do
  an="$(a_n "$n")"
  [ -z "$an" ] && { printf "%d\tNA\n" "$n" >> "$OUTQ"; n=$((n+1)); continue; }
  printf "%d\t%d\n" "$n" "$an" >> "$OUTQ"
  n=$((n+1))
done

# 2.3 smooth L-values: L(1,f) ≈ Σ a_n / n * exp(-n/X), choose X ~ sqrt(M_MAX)
X=$(awk -v M="$M_MAX" 'BEGIN{print sqrt(M)}')
L1=$(awk -v X="$X" '
  BEGIN{sum=0}
  NR>1 && $2!="NA"{ n=$1; an=$2; sum += an/(n)*exp(-n/X) }
  END{printf "%.12f\n", sum}
' "$OUTQ")

Lhalf=$(awk -v X="$X" '
  BEGIN{sum=0}
  NR>1 && $2!="NA"{ n=$1; an=$2; sum += an/(sqrt(n))*exp(-n/X) }
  END{printf "%.12f\n", sum}
' "$OUTQ")

# 2.4 pass criteria: All recorded primes satisfy Hasse, enough coverage, L(1) finite
tot=$(awk 'END{print NR-1}' "$OUTP")
viol=$(awk 'NR>1 && $3=="0"{c++} END{print c+0}' "$OUTP")
coverage_ok=$([ "$tot" -ge 20 ] && echo true || echo false)
hasse_ok=$([ "$viol" -eq 0 ] && echo true || echo false)

# 2.5 JSON leaf (stable order, no timestamps)
jq -n --arg curve "$CURVE" --argjson N "$N" \
      --argjson primes "$tot" --arg hasse "$hasse_ok" --arg coverage "$coverage_ok" \
      --arg L1 "$L1" --arg Lhalf "$Lhalf" \
      '{form:"11a1", curve:$curve, conductor:$N, primes_checked:$primes, hasse_ok:($hasse=="true"), coverage_ok:($coverage=="true"), L1:$L1, Lhalf:$Lhalf, pass:( ($hasse=="true") and ($coverage=="true") )}' \
      > "$OUTJ"

echo "[hecke:11a1] primes=$tot hasse_ok=$hasse_ok L1=$L1"
$([ "$hasse_ok" = true ] && [ "$coverage_ok" = true ])
