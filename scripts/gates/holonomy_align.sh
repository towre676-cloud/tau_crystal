#!/usr/bin/env bash
# Holonomy alignment gate: Explorer (d) vs Seifert angles (A), euler class e
# INI input example:
#   p=7
#   base=10
#   b_int=0
#   chi_sign=0         # +1 / 0 / -1 for χ(B) positive/zero/negative (you can compute elsewhere)
#   pairs= (2:1),(3:1),(6:1)

set -euo pipefail; umask 022; export LC_ALL=C LANG=C

ini="$1"
[ -f "$ini" ] || { echo "usage: $0 CONFIG.ini" >&2; exit 2; }

# --- parse INI (no spaces around '=' please) ---
get(){ awk -F= -v k="$1" '
  $0 !~ /^#/ && $1==k {sub(/^[[:space:]]+/,"",$2); sub(/[[:space:]]+$/,"",$2); print $2; exit }' "$ini"; }
P="$(get p)"; BASE="$(get base)"; BINT="$(get b_int)"; CHI="$(get chi_sign)"
PAIRS_RAW="$(get pairs)"

# normalize pairs " (a:b),(c:d) " -> "a:b c:d"
PAIRS="$(printf "%s\n" "$PAIRS_RAW" | tr -d ' \t' | sed 's/[()]/ /g; s/,/ /g' | awk 'NF{print}' )"

# --- small integer helpers ---
gcd(){ # gcd a b
  awk -v a="$1" -v b="$2" 'function A(a,b){while(b){t=a%b; a=b; b=t} return a} BEGIN{print A(a<0?-a:a,b<0?-b:b)}'
}
lcm2(){ awk -v a="$1" -v b="$2" 'function G(a,b){while(b){t=a%b;a=b;b=t}return a} BEGIN{if(a==0||b==0){print 0;exit} g=G(a<0?-a:a,b<0?-b:b); print (a/g)*b }' ; }
powmod(){ # powmod a e m
  awk -v A="$1" -v E="$2" -v M="$3" 'function mm(a,b,m){return (a*b)%m}
    BEGIN{A%=M; if(A<0)A+=M; r=1; e=E; x=A; while(e>0){ if(e%2==1) r=(r*x)%M; x=(x*x)%M; e=int(e/2);} print r }'
}

# --- validations ---
if [ -z "${P:-}" ] || [ -z "${BASE:-}" ] || [ -z "${BINT:-}" ] || [ -z "${CHI:-}" ] || [ -z "${PAIRS:-}" ]; then
  echo "error: missing required fields in $ini" >&2; exit 3
fi
if ! awk -v p="$P" 'BEGIN{exit !(p>2 && p==int(p))}'; then
  echo "error: p must be integer >2" >&2; exit 3
fi
# base must be coprime to p
G=$(gcd "$BASE" "$P")
if [ "$G" -ne 1 ]; then
  echo "error: base and p must be coprime; gcd(base,p)="$G >&2; exit 3
fi

# --- multiplicative order d = ord_p(BASE) ---
phi=$((P-1))
# factor phi (trial division is enough for small primes used in Explorer UI)
fac=""
m="$phi"
i=2
while [ $((i*i)) -le "$m" ]; do
  if [ $((m%i)) -eq 0 ]; then
    fac="$fac $i"
    while [ $((m%i)) -eq 0 ]; do m=$((m/i)); done
  fi
  i=$((i+1))
done
[ "$m" -gt 1 ] && fac="$fac $m"

d="$phi"
for q in $fac; do
  while [ $((d%q)) -eq 0 ]; do
    cand=$((d/q))
    if [ "$(powmod "$BASE" "$cand" "$P")" -eq 1 ]; then d="$cand"; else break; fi
  done
done

# --- parse pairs and compute A = lcm(a_i), e = b + sum(b_i/a_i) (in lowest terms) ---
A=1
EN=0  # e numerator
ED=1  # e denominator
for ab in $PAIRS; do
  a="${ab%%:*}"; b="${ab#*:}"
  if ! awk -v a="$a" -v b="$b" 'BEGIN{exit !(a==int(a) && a>0 && b==int(b))}'; then
    echo "error: bad pair $ab (expect a>0 integer, b integer)" >&2; exit 4
  fi
  A=$(lcm2 "$A" "$a")
  # EN/ED += b/a  => EN = EN*a + b*ED ; ED = ED*a ; reduce
  EN=$((EN*a + b*ED))
  ED=$((ED*a))
  gg=$(gcd "$EN" "$ED")
  EN=$((EN/gg)); ED=$((ED/gg))
done
# add b_int: e = b_int + EN/ED => (EN + b_int*ED)/ED
EN=$((EN + BINT*ED))
gg=$(gcd "$EN" "$ED"); EN=$((EN/gg)); ED=$((ED/gg))

# --- divisibility and quotient ---
Q=0; DIV="false"
if [ $((A%d)) -eq 0 ]; then Q=$((A/d)); DIV="true"; fi

# --- verdict from χ and e ---
# χ: +1 -> SPHERE / S2xR; 0 -> EUCLIDEAN or NIL; -1 -> SL2R or H2xR by split
REGIME=""
SPLIT="false"   # e == 0?
[ "$EN" -eq 0 ] && SPLIT="true"
case "$CHI" in
  1)   REGIME="SPHERE_or_S2xR" ;;
  0)   if [ "$SPLIT" = "true" ]; then REGIME="EUCLIDEAN"; else REGIME="NIL"; fi ;;
 -1)   if [ "$SPLIT" = "true" ]; then REGIME="H2xR"; else REGIME="SL2R_tilde"; fi ;;
  *)   REGIME="UNKNOWN" ;;
esac

# --- JSON receipt (no jq) ---
ts="$(date -u +%Y%m%dT%H%M%SZ)"
cat <<JSON
{
  "timestamp_utc": "$ts",
  "prime_p": $P,
  "base_b": $BASE,
  "ord_d": $d,
  "A_lcm": $A,
  "divides": $DIV,
  "cover_index_Q": $Q,
  "euler_class": { "numer": $EN, "denom": $ED, "is_zero": $( [ "$SPLIT" = "true" ] && echo true || echo false ) },
  "chi_sign": $CHI,
  "regime": "$REGIME",
  "pairs": [$(printf "%s" "$PAIRS" | awk 'BEGIN{f=1}{split($0,a,":"); if(!f)printf(","); f=0; printf("{\"a\":%d,\"b\":%d}",a[1],a[2])}') ]
}
JSON
