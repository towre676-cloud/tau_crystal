#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C

usage(){ echo "usage: $0 cases/<name>.ini"; exit 64; }
[ $# -ne 1 ] && usage
INI="$1"; [ -f "$INI" ] || { echo "[err] missing case ini: $INI" >&2; exit 66; }

# ini read (no jq). trims spaces; ignores comments and blank lines.
trim(){ sed -e "s/^[[:space:]]*//" -e "s/[[:space:]]*$//"; }
val(){ grep -E "^[[:space:]]*$1[[:space:]]*=" "$INI" | tail -n1 | cut -d= -f2- | trim; }
P=$(val prime_p); B=$(val base_b); EB=$(val euler_b)
ANGS=$(val seifert_angles)
[ -n "${P:-}" ] && [ -n "${B:-}" ] && [ -n "${ANGS:-}" ] || { echo "[err] bad ini"; exit 65; }

# gcd, lcm, powmod, order with awk (small ints)
gcd(){ a=$1; b=$2; while [ "$b" -ne 0 ]; do t=$((a%%b)); a=$b; b=$t; done; echo "${a#-}"; }
lcm(){ a=$1; b=$2; g=$(gcd "$a" "$b"); echo $(( (a/g)*b )); }
powmod(){ awk -v a="$1" -v e="$2" -v m="$3" 'function pm(a,e,m, r){r=1;a=((a%%m)+m)%%m;while(e>0){if(e%2==1)r=(r*a)%m;a=(a*a)%m;e=int(e/2)}return r} BEGIN{print pm(a,e,m)}'; }
isprime(){ n=$1; [ "$n" -ge 2 ] || return 1; i=2; while [ $((i*i)) -le "$n" ]; do [ $((n%%i)) -eq 0 ] && return 1; i=$((i+1)); done; return 0; }
ord(){ a=$1; p=$2; [ $((a%%p)) -eq 0 ] && { echo 0; return; }; phi=$((p-1)); # factor phi
  fs=""; m=$phi; q=2; while [ $((q*q)) -le "$m" ]; do if [ $((m%%q)) -eq 0 ]; then fs="$fs $q"; while [ $((m%%q)) -eq 0 ]; do m=$((m/q)); done; fi; q=$((q+1)); done; [ "$m" -gt 1 ] && fs="$fs $m"
  o=$phi; for q in $fs; do while [ $((o%%q)) -eq 0 ]; do cand=$((o/q)); pm=$(powmod "$a" "$cand" "$p"); if [ "$pm" -eq 1 ]; then o=$cand; else break; fi; done; done; echo "$o"; }

# compute A=lcm(a_i), check divisibility, classify by chi/euler
A=1; chi_adj=0; bad=""
for pair in $(echo "$ANGS" | tr "," " "); do ai=${pair%%:*}; bi=${pair##*:}; [ -n "$ai" ] && [ -n "$bi" ] || { echo "[err] bad pair: $pair"; exit 65; }
  A=$(lcm "$A" "$ai")
  # for chi(B)=chi(B0)-sum(1-1/ai) we only accumulate the orbifold correction here
  chi_adj=$(awk -v s="$chi_adj" -v a="$ai" 'BEGIN{print s + (1.0 - 1.0/a)}')
done

isprime "$P" || { echo "[err] P not prime"; exit 65; }
[ $((B%%P)) -eq 0 ] && { echo "[err] base shares factor with p"; exit 65; } || true
D=$(ord "$B" "$P")
divides=$(( A%%D ))

# crude regime flag: we do not parse B0; we report the sign bucket driven by the orbifold correction and Euler class
E=${EB:-0}
regime="unknown"; split=""; if awk -v c="$chi_adj" 'BEGIN{exit !(c<0)}'; then regime="POSITIVE_orbifold"; elif awk -v c="$chi_adj" 'BEGIN{exit !(c==0)}'; then regime="ZERO_orbifold"; else regime="NEGATIVE_orbifold"; fi
if [ "$regime" = "ZERO_orbifold" ]; then if awk -v e="$E" 'BEGIN{exit !(e==0)}'; then split="EUCLIDEAN"; else split="NIL"; fi; fi

ts=$(date -u +%Y%m%dT%H%M%SZ)
echo "[holonomy] p=$P base=$B ord_d=$D A_lcm=$A euler_b=$E chi_adj=$(printf "%.6f" "$chi_adj") regime=$regime split=$split time=$ts"
echo "MACHINE p=$P b=$B d=$D A=$A eB=$E chiAdj=$(printf "%.6f" "$chi_adj") regime=$regime split=$split ts=$ts"
[ "$divides" -eq 0 ] || { echo "[verdict] FAIL: d does not divide A"; exit 1; }
echo "[verdict] PASS: holonomy aligns (d|A)."

