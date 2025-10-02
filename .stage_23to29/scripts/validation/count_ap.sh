#!/usr/bin/env bash
set -euo pipefail; set +H; . scripts/validation/_util.sh
CURVE="$1"; OUTP="$2"; OUTN="$3"; PR="validation/work/primes_1000.txt"
read _A A < <(grep -m1 "^A	" "$CURVE"); read _B B < <(grep -m1 "^B	" "$CURVE")
rm -f "$OUTP"; touch "$OUTP"
while read -r p; do
  pts=1
  for ((x=0;x<p;x++)); do
    rhs=$(( ( ((x*x%p)*x)%p + (A%p+p)%p * x )%p )); rhs=$(( (rhs + (B%p+p)%p )%p ))
    chi=$(legendre $rhs $p)
    if [ $chi -eq 0 ]; then pts=$((pts+1)); elif [ $chi -eq 1 ]; then pts=$((pts+2)); fi
  done
  ap=$(( p + 1 - pts ))
  printf "%s\t%s\n" "$p" "$ap" >> "$OUTP"
done < "$PR"
limit=1000; rm -f "$OUTN"; printf "1\t1\n" > "$OUTN"
declare -A AP; while read p v; do AP[$p]=$v; done < "$OUTP"
for ((n=2;n<=limit;n++)); do
  m=$n; an=1; q=2
  while [ $((q*q)) -le $m ]; do
    if [ $((m%q)) -eq 0 ]; then
      k=0; while [ $((m%q)) -eq 0 ]; do m=$((m/q)); k=$((k+1)); done
      if [ -z "${AP[$q]:-}" ]; then aqk=1
      else
        a1=${AP[$q]}
        if [ $k -eq 1 ]; then aqk=$a1
        else a_prev=$a1; a_prev2=1; for ((t=2;t<=k;t++)); do a_now=$(( a1*a_prev - q*a_prev2 )); a_prev2=$a_prev; a_prev=$a_now; done; aqk=$a_prev
        fi
      fi
      an=$((an * aqk))
    fi
    q=$((q+1))
  done
  if [ $m -gt 1 ]; then q=$m; aqk=${AP[$q]:-1}; an=$((an*aqk)); fi
  printf "%s\t%s\n" "$n" "$an" >> "$OUTN"
done
