#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
export LC_NUMERIC=C

mkdir -p tsv logs

# Basis constants (decimals)
alpha='0.0072973525693'        # 1/137.035999084
alphas='0.1179'
pi_val='3.141592653589793'
phi_val='1.6180339887498948'
mp_me='1836.15267343'

# numeric helper: supports decimal or a/b, outputs decimal
rf(){ awk -v x="$1" 'BEGIN{if(x~/\//){split(x,t,"/");v=(t[1]+0)/(t[2]+0)}else v=x+0; printf("%.15g",v)}'; }

# basis logs
ln_alpha="$(awk -v x="$(rf "$alpha")"  'BEGIN{printf("%.15g",log(x)+0.0)}')"
ln_alphas="$(awk -v x="$(rf "$alphas")" 'BEGIN{printf("%.15g",log(x)+0.0)}')"
ln_pi="$(awk -v x="$(rf "$pi_val")"    'BEGIN{printf("%.15g",log(x)+0.0)}')"
ln_phi="$(awk -v x="$(rf "$phi_val")"  'BEGIN{printf("%.15g",log(x)+0.0)}')"
ln_mpme="$(awk -v x="$(rf "$mp_me")"   'BEGIN{printf("%.15g",log(x)+0.0)}')"

echo "Z basis:" 1>&2
printf "  ln_alpha   = %s\n  ln_alpha_s = %s\n  ln_pi      = %s\n  ln_phi     = %s\n  ln_mp/me   = %s\n" \
  "$ln_alpha" "$ln_alphas" "$ln_pi" "$ln_phi" "$ln_mpme" 1>&2

# search settings
DENOMS=(7 9 11 12)
P_MAX=8
MDL_LAMBDA="0.0001"
BOOTSTRAP_N=5000
RANDOM_SEED=42

BEST_TSV="tsv/ulp_search_best.tsv"
BUCKET_TSV="tsv/ulp_search_bucket.tsv"
KAPPA_TXT="tsv/ulp_kappa_bootstrap.txt"

search_one(){ awk -v y="$1" -v sig="$2" -v Dmax="$3" \
  -v P="$P_MAX" -v mdl="$MDL_LAMBDA" \
  -v z0="$ln_alpha" -v z1="$ln_alphas" -v z2="$ln_pi" -v z3="$ln_phi" -v z4="$ln_mpme" '
  function bic(eps,k,maxq,nobs){ nobs=5; chi2=(sig>0?(eps*eps)/(sig*sig):1e12*eps*eps); return chi2+k*log(nobs)+(mdl+0.0)*maxq }
  function add(r0,r1,r2,r3,r4,eps,k,maxq){ B=bic(eps,k,maxq); if(B<best-1e-15){best=B;m=0} if(B<=best+2+1e-15){S[m,0]=r0;S[m,1]=r1;S[m,2]=r2;S[m,3]=r3;S[m,4]=r4;S[m,5]=eps;S[m,6]=k;S[m,7]=maxq;SB[m]=B;m++}}
  function scan_single(i){ for(q=1;q<=Dmax;q++)for(p=-P;p<=P;p++){ if(p==0)continue; r0=r1=r2=r3=r4=0; v=p/q; (i==0)?r0=v:(i==1)?r1=v:(i==2)?r2=v:(i==3)?r3=v:r4=v; yhat=r0*z0+r1*z1+r2*z2+r3*z3+r4*z4; eps=y-yhat; add(r0,r1,r2,r3,r4,eps,1,q)} }
  function scan_pair(i,j){ for(q1=1;q1<=Dmax;q1++)for(p1=-P;p1<=P;p1++)for(q2=1;q2<=Dmax;q2++)for(p2=-P;p2<=P;p2++){ if(p1==0&&p2==0)continue; r0=r1=r2=r3=r4=0; v1=p1/q1; v2=p2/q2; (i==0)?r0=v1:(i==1)?r1=v1:(i==2)?r2=v1:(i==3)?r3=v1:r4=v1; (j==0)?r0=v2:(j==1)?r1=v2:(j==2)?r2=v2:(j==3)?r3=v2:r4=v2; yhat=r0*z0+r1*z1+r2*z2+r3*z3+r4*z4; eps=y-yhat; k=(p1!=0)+(p2!=0); maxq=(q1>q2?q1:q2); add(r0,r1,r2,r3,r4,eps,k,maxq)} }
  BEGIN{best=1e99;m=0}
  END{
    for(i=0;i<5;i++) scan_single(i)
    for(i=0;i<5;i++) for(j=i+1;j<5;j++) scan_pair(i,j)
    if(m==0){print "NA"; exit}
    besti=-1; bestchi=1e99;
    for(i=0;i<m;i++){ eps=S[i,5]; chi=(sig>0?(eps*eps)/(sig*sig):1e12*eps*eps); if(chi<bestchi){bestchi=chi;besti=i}}
    printf "%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%d\t%d\t%.6f\t%d\n", S[besti,0],S[besti,1],S[besti,2],S[besti,3],S[besti,4], S[besti,5], (sig>0?S[besti,5]/sig:0/0), S[besti,6], S[besti,7], best, m
    for(i=0;i<m;i++) printf "BUCKET\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%d\t%d\t%.6f\n", S[i,0],S[i,1],S[i,2],S[i,3],S[i,4], S[i,5], (sig>0?S[i,5]/sig:0/0), S[i,6], S[i,7], SB[i]
  }'; }

orbit_stats(){ awk -v r0="$1" -v r1="$2" -v r2="$3" -v r3="$4" -v r4="$5" '
  function absv(x){return x<0?-x:x} function keyf(x){return sprintf("%.12f",x)}
  function fact(n,  i,f){f=1; for(i=2;i<=n;i++) f*=i; return f}
  BEGIN{ r[1]=r0;r[2]=r1;r[3]=r2;r[4]=r3;r[5]=r4; z=0; for(i=1;i<=5;i++){v[i]=absv(r[i]); if(v[i]==0) z++}
        for(i=1;i<=5;i++){ if(v[i]==0)continue; k=keyf(v[i]); cnt[k]++ }
        stab=1; for(i=1;i<=z;i++) stab*=2; mults=""; for(k in cnt){m=cnt[k]; stab*=fact(m); mults=mults sprintf("%s:%d,",k,m)} if(length(mults)>0) sub(/,$/,"",mults); orbit=int(3840/(stab>0?stab:1)); print stab, orbit, mults }'; }

# Write best/bucket TSVs
{
  echo -e "name\tDmax\ty\tsigma\tr0\tr1\tr2\tr3\tr4\tresidual\tz\tk\tmaxQ\tBIC\tbucketN\tstab\torbit\tmults"
  awk 'NR>1 && $1!~/^#/{gsub(/[[:space:]]+/,"\t"); print $1"\t"$2"\t"$3}' tsv/ulp_panel.tsv | \
  while IFS=$'\t' read -r nm y s; do
    for D in 7 9 11 12; do
      MAP="$(search_one "$y" "$s" "$D")"
      IFS=$'\n' read -r rep <<< "$MAP"
      IFS=$'\t' read -r r0 r1 r2 r3 r4 eps z k maxQ BIC m <<< "$rep"
      read -r stab orbit mults < <(orbit_stats "$r0" "$r1" "$r2" "$r3" "$r4")
      printf "%s\t%d\t%.12g\t%.12g\t%s\t%s\t%s\t%s\t%s\t%.12g\t%.12g\t%d\t%d\t%.6f\t%d\t%d\t%d\t%s\n" \
        "$nm" "$D" "$y" "$s" "$r0" "$r1" "$r2" "$r3" "$r4" "$eps" "$z" "$k" "$maxQ" "$BIC" "$m" "$stab" "$orbit" "$mults"
      echo "$MAP" | awk -v nm="$nm" -v D="$D" 'BEGIN{hdr=0} /^BUCKET\t/{ if(hdr==0){ print "name\tDmax\tr0\tr1\tr2\tr3\tr4\teps\tz\tk\tmaxQ\tBIC"; hdr=1 } $1=""; sub(/^\t/,""); print nm"\t"D"\t"$0 }'
    done
  done
} > "$BEST_TSV" | tee "$BUCKET_TSV" >/dev/null

# κ bootstrap (D=12)
mapfile -t RES < <(awk -F'\t' 'NR>1 && $2==12 {print $10}' "$BEST_TSV")
awk -v B="$BOOTSTRAP_N" -v seed="$RANDOM_SEED" '
  function kappa(a,n,   i,I1,I2){I1=I2=0; for(i=1;i<=n;i++){I1+=a[i]^2; I2+=a[i]^4} return (I1>0?5*(I2/(I1*I1))-3:0/0) }
  BEGIN{ n=ARGC-1; if(n<2){print "kappa: NA (need ≥2 residuals)"; exit}
         for(i=1;i<=n;i++) e[i]=ARGV[i]; k0=kappa(e,n); srand(seed);
         for(b=1;b<=B;b++){ for(i=1;i<=n;i++){j=1+int(rand()*n); eb[i]=e[j]} kb[kbN++]=kappa(eb,n) }
         for(i=1;i<kbN;i++) for(j=i+1;j<=kbN;j++) if(kb[j]<kb[i]){t=kb[i];kb[i]=kb[j];kb[j]=t}
         lo=kb[int(0.16*B)]; hi=kb[int(0.84*B)];
         printf "kappa_bootstrap: k0=%.6f, 68%% CI [%.6f, %.6f], N=%d\n", k0, lo, hi, n }' "${RES[@]}" | tee "$KAPPA_TXT"

echo "Wrote:"
echo "  $BEST_TSV"
echo "  $BUCKET_TSV"
echo "  $KAPPA_TXT"
