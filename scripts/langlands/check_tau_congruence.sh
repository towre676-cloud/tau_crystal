#!/usr/bin/env bash
set +H
umask 022
SEQ="analysis/validation/face_tau_sequences.tsv"
OUT="analysis/validation/tau_congruence_report.tsv"
[ ! -f "$SEQ" ] && { echo "missing: $SEQ" >&2; exit 2; }
: > "$OUT"
printf "face_id\tprime\tap\t(1+p^11)%%691\tok_mod_691\tdeligne_bound\tok_deligne\n" >> "$OUT"
PRIMES="2 3 5 7 11 13 17 19 23 29 31 37"
awk -v PRIMES="$PRIMES" -F"\t" 'BEGIN{ split(PRIMES,P," "); M=691 }
NR==1{ next }
{ face=$1; seq=$3; n=split(seq,A,/[, ]+/);
  for(i=1;i<=length(P)&&i<=n;i++){
    ap=A[i]; if(ap==""||ap=="NA") continue; p=P[i]+0;
    # compute (1+p^11) mod 691
    r=1; for(k=1;k<=11;k++){ r=(r*(p%M))%M } modref=(1+r)%M;
    gsub(/[^0-9+-]/,"",ap); if(ap=="+"||ap=="-") next; apv=ap+0; apm=apv%M; if(apm<0) apm+=M;
    ok=(apm==modref?"yes":"no");
    # Deligne bound |tau(p)| <= 2 p^(11/2)
    bound = 2*exp(0.5*11*log(p)); okd=( (apv<=bound && -apv<=bound) ? "yes" : "no");
    printf "%s\t%d\t%d\t%d\t%s\t%.6f\t%s\n", face,p,apv,modref,ok,bound,okd
  }
}' "$SEQ" >> "$OUT"
awk '{ sub(/\r$/,""); print }' "$OUT" > "$OUT.tmp" && mv "$OUT.tmp" "$OUT"
echo "wrote $OUT"
