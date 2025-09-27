#!/usr/bin/env bash
# Chebyshev moments gate (Explorer spectral probe)
# INI input (example):
#   p=7
#   base=10
#   K=12                # how many moments to compute (n=1..K)
#   center=1            # 1 => subtract mean before moments; 0 => raw digits
#
# Output: JSON with ord_d, repetend (length d), dc, and moments[1..K].

set -euo pipefail; umask 022; export LC_ALL=C LANG=C

ini="${1:-}"
[ -n "$ini" ] && [ -f "$ini" ] || { echo "usage: $0 CONFIG.ini" >&2; exit 2; }

# --- parse INI ---
get(){ awk -F= -v k="$1" '$0 !~ /^#/ && $1==k {sub(/^[[:space:]]+/,"",$2);sub(/[[:space:]]+$/,"",$2);print $2;exit}' "$ini"; }
P="$(get p)"; BASE="$(get base)"; K="$(get K)"; CENTER="${CENTER_OVERRIDE:-$(get center 2>/dev/null || echo 1)}"

[ -n "${P:-}" ] && [ -n "${BASE:-}" ] && [ -n "${K:-}" ] || { echo "missing required keys p/base/K in $ini" >&2; exit 3; }
awk -v p="$P" 'BEGIN{exit !(p>2 && p==int(p))}' || { echo "p must be integer > 2" >&2; exit 3; }
awk -v b="$BASE" 'BEGIN{exit !(b>=2 && b==int(b))}' || { echo "base must be integer >= 2" >&2; exit 3; }
awk -v k="$K" 'BEGIN{exit !(k>=1 && k==int(k))}' || { echo "K must be integer >= 1" >&2; exit 3; }

# --- helpers: gcd, lcm, powmod, ord_p(base) ---
gcd(){ awk -v a="$1" -v b="$2" 'function G(a,b){while(b){t=a%b;a=b;b=t}return (a<0?-a:a)} BEGIN{print G(a,b)}'; }
powmod(){ awk -v A="$1" -v E="$2" -v M="$3" 'BEGIN{A%=M; if(A<0)A+=M; r=1; x=A; e=E; while(e>0){ if(e%2) r=(r*x)%M; x=(x*x)%M; e=int(e/2);} print r }'; }

# require coprime base/p
if [ "$(gcd "$BASE" "$P")" -ne 1 ]; then
  echo "error: base and p must be coprime (gcd != 1)" >&2; exit 4
fi

phi=$((P-1))
# factor phi (trial division)
fac=""
m="$phi"; i=2
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

# --- build repetend digits for 1/p in base (length d) ---
# long division: rem_{i+1} = (rem_i * base) % p ; digit_i = floor((rem_i * base)/p)
digits="$(awk -v p="$P" -v b="$BASE" -v d="$d" '
  BEGIN{
    rem = 1 % p;
    if(rem<0) rem+=p;
    for(i=0;i<d;i++){
      t = rem * b;
      digit = int(t / p);
      rem = t % p;
      printf("%d", digit);
      if(i<d-1) printf(" ");
    }
  }')"

# compute mean (DC)
dc="$(awk -v s="$digits" -v d="$d" '
  BEGIN{
    n=split(s,a," ");
    tot=0; for(i=1;i<=n;i++) tot+=a[i];
    printf("%.12f", tot/d);
  }')"

# choose vector: centered or raw
vec="$(if [ "${CENTER:-1}" -eq 1 ]; then
  awk -v s="$digits" -v mu="$dc" 'BEGIN{n=split(s,a," "); for(i=1;i<=n;i++){ printf("%s%.12f", (i==1?"":" "), a[i]-mu);} }'
else
  echo "$digits" | awk '{for(i=1;i<=NF;i++) printf("%s%.12f",(i==1?"":" "),$i)}'
fi)"

# moments μ_n = Σ_k v_k cos(2π n k / d), k=0..d-1, n=1..K
# use gawk cos() and pi=atan2(0,-1) trick
moments="$(awk -v V="$vec" -v d="$d" -v K="$K" '
  BEGIN{
    pi = atan2(0,-1);
    n = split(V,v," ");
    if(n!=d){ d=n; }
    for(m=1;m<=K;m++){
      mu = 0.0;
      for(k=0;k<d;k++){
        x = v[k+1];
        theta = 2.0*pi*m*k/d;
        mu += x * cos(theta); # Chebyshev T_m(cos(2πk/d)) == cos(m*2πk/d)
      }
      printf((m==1?"":" ") "%.12f", mu);
    }
  }')"

# JSON (no jq)
ts="$(date -u +%Y%m%dT%H%M%SZ)"
printf '{\n'
printf '  "timestamp_utc": "%s",\n' "$ts"
printf '  "prime_p": %d,\n' "$P"
printf '  "base_b": %d,\n' "$BASE"
printf '  "ord_d": %d,\n' "$d"
printf '  "K": %d,\n' "$K"
printf '  "centered": %s,\n' "$([ "${CENTER:-1}" -eq 1 ] && echo true || echo false)"
printf '  "dc": %.12f,\n' "$dc"
# repetend digits as string to be compact (no quotes per-digit)
repstr="$(echo "$digits" | tr -d ' ')"
printf '  "repetend_digits": "%s",\n' "$repstr"
printf '  "moments": ['
# print array
awk -v s="$moments" 'BEGIN{n=split(s,a," "); for(i=1;i<=n;i++){ if(i>1) printf(","); printf("%s", a[i]); }}'
printf ']\n}\n'
