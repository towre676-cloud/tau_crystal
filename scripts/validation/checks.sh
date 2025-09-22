#!/usr/bin/env bash
set -euo pipefail; set +H
ROOT="${1:-validation/work}"
OUT="analysis/validation/tau_congruence_report.tsv"
printf "face\tp\tap\tmod691_ok\tdeligne_ok\tintegral\tmultiplicativity_checked\tstable\n" > "$OUT"
fail=0
for D in "$ROOT"/face*/; do [ -d "$D" ] || continue; face="$(basename "$D")"; AP="$D/a_p.tsv"; [ -s "$AP" ] || { echo "WARN $face: missing a_p.tsv"; continue; }
  while IFS=$'\t' read -r p ap; do case "$p" in ""|[!0-9]*) continue;; esac
    intok=0; if printf "%s" "$ap" | grep -Eq "^-?[0-9]+$"; then intok=1; fi
    if [ "$p" -ge 5 ]; then
      modp=$(awk -v p="$p" 'function modexp(b,e,m, r){r=1%m;b%=m;for(i=0;i<e;i++){r=(r*b)%m}return r} BEGIN{print (1+modexp(p,11,691))%691}')
      diff=$(( ( (ap % 691) + 691 ) % 691 ))
      exp=$(( ( (modp % 691) + 691 ) % 691 ))
      m691=$([ "$diff" -eq "$exp" ] && echo ok || echo FAIL)
    else m691="skip"; fi
    delok=$(awk -v p="$p" -v ap="$ap" 'BEGIN{b=2*exp( (11/2)*log(p) ); if(ap<0) ap=-ap; print (ap<=b+1e-6)?"ok":"FAIL"}')
    mult="skip"; stab="skip";
    printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$face" "$p" "$ap" "$m691" "$delok" "$([ "$intok" -eq 1 ] && echo ok || echo FAIL)" "$mult" "$stab" >> "$OUT"
    [ "$m691" = "FAIL" ] && fail=1
    [ "$delok" = "FAIL" ] && fail=1
    [ "$intok" -eq 1 ] || fail=1
  done < "$AP"
done
[ "$fail" -eq 0 ] || { echo "Arithmetic checks failed"; exit 2; }
