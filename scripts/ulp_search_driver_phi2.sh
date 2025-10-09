#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
export LC_NUMERIC=C

mkdir -p tsv logs

# Basis (decimals)
alpha='0.0072973525693'      # CODATA 2022
alphas='0.1179'              # PDG @ M_Z
pi_val='3.141592653589793'
phi_val="2"
mp_me='1836.15267343'

llog(){ awk -v x="$1" 'BEGIN{printf("%.15g", log(x)+0.0)}'; }
ln_alpha="$(llog "$alpha")"
ln_alphas="$(llog "$alphas")"
ln_pi="$(llog "$pi_val")"
ln_phi="$(llog "$phi_val")"
ln_mpme="$(llog "$mp_me")"

echo "Z basis:" >&2
printf "  ln_alpha   = %s\n  ln_alpha_s = %s\n  ln_pi      = %s\n  ln_phi     = %s\n  ln_mp/me   = %s\n" \
  "$ln_alpha" "$ln_alphas" "$ln_pi" "$ln_phi" "$ln_mpme" >&2

DENOMS=(7 9 11 12)
P_MAX=2
MDL_LAMBDA=0.1

BEST_TSV="tsv/ulp_search_best.tsv"
BUCKET_TSV="tsv/ulp_search_bucket.tsv"
KAPPA_TXT="tsv/ulp_kappa_bootstrap.txt"
PANEL="tsv/ulp_panel.tsv"

echo -e "name\tDmax\ty\tsigma\tr0\tr1\tr2\tr3\tr4\tresidual\tz\tchi2\tdof\tchi2_dof\tk\tmaxQ\tL1\tBIC\tbucketN\tstab\torbit\tmults" > "$BEST_TSV"
echo -e "name\tDmax\tr0\tr1\tr2\tr3\tr4\teps\tz\tchi2\tk\tmaxQ\tL1\tBIC" > "$BUCKET_TSV"

# Ensure a minimal panel
if [[ ! -s "$PANEL" ]]; then
  printf 'ln_sin_theta12\t-1.490\t0.010\nln_OmegaLambda\t-0.370\t0.006\n' > "$PANEL"
fi

# orbit metadata
orbit_row() {
  awk -v r0="$1" -v r1="$2" -v r2="$3" -v r3="$4" -v r4="$5" '
    function absv(x){return x<0?-x:x}
    function keyf(x){return sprintf("%.12f", x)}
    function two_pow(n, i,p){p=1;for(i=1;i<=n;i++)p*=2;return p}
    function fact(n, i,f){f=1;for(i=2;i<=n;i++)f*=i;return f}
    BEGIN{
      v[1]=absv(r0); v[2]=absv(r1); v[3]=absv(r2); v[4]=absv(r3); v[5]=absv(r4)
      zeros=0
      for(i=1;i<=5;i++){
        if(v[i]==0){zeros++;continue}
        k=keyf(v[i]); cnt[k]++
      }
      stab=two_pow(zeros); mults=""
      for(k in cnt){ m=cnt[k]; stab*=fact(m); mults=mults sprintf("%s:%d,",k,m) }
      if(length(mults)>0) sub(/,$/,"",mults)
      orbit=int(3840/(stab>0?stab:1))
      print stab, orbit, mults
    }'
}

# process panel
while IFS=$'\t' read -r nm y s; do
  [[ -z "${nm// }" || "${nm:0:1}" == "#" ]] && continue
  for D in "${DENOMS[@]}"; do
    # run awk search -> bucket rows
    mapfile -t bucket < <(
      awk -v Y0="$y" -v SIG0="$s" -v DMAX0="$D" -v PMAX0="$P_MAX" -v MDL0="$MDL_LAMBDA" \
          -v Z0v="$ln_alpha" -v Z1v="$ln_alphas" -v Z2v="$ln_pi" -v Z3v="$ln_phi" -v Z4v="$ln_mpme" \
          -f scripts/ulp_search.awk \
      | awk -v nm="$nm" -v D="$D" 'BEGIN{OFS="\t"} $1=="BUCKET"{
           # name D r0..r4 eps z chi2 k maxQ L1 BIC
           print nm, D, $(2),$(3),$(4),$(5),$(6),$(7),$(8),$(9),$(10),$(11),$(12),$(13)
         }'
    )
    # append full bucket
    if ((${#bucket[@]})); then
      printf "%s\n" "${bucket[@]}" >> "$BUCKET_TSV"
      # REP: min maxQ -> min L1 -> min chi2
      rep_line="$(printf "%s\n" "${bucket[@]}" | sort -t $'\t' -k12,12n -k13,13n -k11,11n | head -1)"
      IFS=$'\t' read -r _nm _D r0 r1 r2 r3 r4 eps z chi2 k maxQ L1 bic <<< "$rep_line"
      dof=1; chi2_dof="$chi2"
      read -r stab orbit mults < <(orbit_row "$r0" "$r1" "$r2" "$r3" "$r4")
      echo -e "$nm\t$D\t$y\t$s\t$r0\t$r1\t$r2\t$r3\t$r4\t$eps\t$z\t$chi2\t$dof\t$chi2_dof\t$k\t$maxQ\t$L1\t$bic\t${#bucket[@]}\t$stab\t$orbit\t$mults" \
        >> "$BEST_TSV"
    fi
  done
done < <(awk 'BEGIN{FS=OFS="\t"} /^[ \t]*$/||/^[ \t]*#/ {next} {gsub(/[ \t]+/,"\t"); if(NF>=3)print $1,$2,$3}' "tsv/ulp_panel.tsv")

# kappa from D=12 residuals + 68% bootstrap CI
awk -F'\t' 'NR>1 && $2==12 {x[++n]=$10+0}
END{
  if(n<2){print "kappa: NA (need ≥2)"; exit}
  I1=I2=0; for(i=1;i<=n;i++){I1+=x[i]^2; I2+=x[i]^4}
  k0 = (I1>0? 5*(I2/(I1*I1)) - 3 : 0/0)

  B=5000; srand(42)
  for(b=1;b<=B;b++){
    I1=I2=0
    for(i=1;i<=n;i++){ j=int(1+rand()*n); I1+=x[j]^2; I2+=x[j]^4 }
    kb[b]=(I1>0? 5*(I2/(I1*I1))-3 : 0/0)
  }
  # sort
  for(i=1;i<=B;i++) for(j=i+1;j<=B;j++) if(kb[j]<kb[i]){t=kb[i];kb[i]=kb[j];kb[j]=t}
  lo=kb[int(0.16*B)]; hi=kb[int(0.84*B)]
  printf("kappa (D=12 reps) = %.6g   n = %d   68%% CI = [%.6g, %.6g]\n", k0, n, lo, hi)
}' "$BEST_TSV" > "$KAPPA_TXT"

echo "OK: wrote $BEST_TSV, $BUCKET_TSV, $KAPPA_TXT"
