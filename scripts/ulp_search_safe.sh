#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
export LC_NUMERIC=C

mkdir -p tsv logs

# Basis (decimals)
alpha='0.0072973525693'      # CODATA 2022
alphas='0.1179'              # PDG @ M_Z
pi_val='3.141592653589793'
phi_val='1.6180339887498948'
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
P_MAX=8
MDL_LAMBDA=0.0001

BEST_TSV="tsv/ulp_search_best.tsv"
BUCKET_TSV="tsv/ulp_search_bucket.tsv"
KAPPA_TXT="tsv/ulp_kappa_bootstrap.txt"

# --- AWK search program to temp file (robust here-doc) ---
AWK_SEARCH_FILE="$(mktemp)"
cat > "$AWK_SEARCH_FILE" <<'AWKPROG'
function bic(eps,k,maxq, nobs){ nobs=5; chi2=(SIG>0?(eps*eps)/(SIG*SIG):1e12*eps*eps); return chi2+k*log(nobs)+(MDL+0.0)*maxq }
function add(r0,r1,r2,r3,r4,eps,k,maxq){ B=bic(eps,k,maxq); if(B<best-1e-15){best=B;m=0} if(B<=best+2+1e-15){S[m,0]=r0;S[m,1]=r1;S[m,2]=r2;S[m,3]=r3;S[m,4]=r4;S[m,5]=eps;S[m,6]=k;S[m,7]=maxq;SB[m]=B;m++}}
function sc1(i, q,p,v,yhat){ for(q=1;q<=DMAX;q++){ for(p=-PMAX;p<=PMAX;p++){ if(p==0)continue; v=p/q;
  r0=r1=r2=r3=r4=0; (i==0)?r0=v:(i==1)?r1=v:(i==2)?r2=v:(i==3)?r3=v:r4=v;
  yhat=r0*Z0+r1*Z1+r2*Z2+r3*Z3+r4*Z4; add(r0,r1,r2,r3,r4,Y-yhat,1,q) }}}
function sc2(i,j, q1,p1,q2,p2,v1,v2,yhat,k,maxq){ for(q1=1;q1<=DMAX;q1++){ for(p1=-PMAX;p1<=PMAX;p1++){
  for(q2=1;q2<=DMAX;q2++){ for(p2=-PMAX;p2<=PMAX;p2++){
    if(p1==0&&p2==0)continue; v1=p1/q1; v2=p2/q2;
    r0=r1=r2=r3=r4=0; (i==0)?r0=v1:(i==1)?r1=v1:(i==2)?r2=v1:(i==3)?r3=v1:r4=v1;
                      (j==0)?r0=v2:(j==1)?r1=v2:(j==2)?r2=v2:(j==3)?r3=v2:r4=v2;
    yhat=r0*Z0+r1*Z1+r2*Z2+r3*Z3+r4*Z4; k=(p1!=0)+(p2!=0); maxq=(q1>q2?q1:q2); add(r0,r1,r2,r3,r4,Y-yhat,k,maxq)
}}}}
BEGIN{
  Y=Y0+0; SIG=SIG0+0; DMAX=DMAX0; PMAX=PMAX0; MDL=MDL0;
  Z0=Z0v; Z1=Z1v; Z2=Z2v; Z3=Z3v; Z4=Z4v;
  best=1e99; m=0;
  for(i=0;i<5;i++) sc1(i)
  for(i=0;i<5;i++) for(j=i+1;j<5;j++) sc2(i,j)
  if(m==0){print "NA"; exit}
  besti=-1; bestchi=1e99
  for(i=0;i<m;i++){ eps=S[i,5]; chi=(SIG>0?(eps*eps)/(SIG*SIG):1e12*eps*eps); if(chi<bestchi){bestchi=chi;besti=i} }
  # representative
  printf "REP\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%d\t%d\t%.6f\t%d\n",
         S[besti,0],S[besti,1],S[besti,2],S[besti,3],S[besti,4],
         S[besti,5], (SIG>0?S[besti,5]/SIG:0), S[besti,6], S[besti,7], best, m
  # bucket
  for(i=0;i<m;i++)
    printf "BUCKET\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%d\t%d\t%.6f\n",
           S[i,0],S[i,1],S[i,2],S[i,3],S[i,4], S[i,5], (SIG>0?S[i,5]/SIG:0), S[i,6], S[i,7], SB[i]
}
AWKPROG

# Ensure LF endings on Windows shells
command -v dos2unix >/dev/null 2>&1 && dos2unix -q "$AWK_SEARCH_FILE" || true

# Normalize panel to TABs, then stream as space-separated triples
PANEL_TMP="$(mktemp)"
awk '
  BEGIN{OFS="\t"}
  /^[[:space:]]*$/ || /^[[:space:]]*#/ {next}
  { gsub(/[[:space:]]+/, "\t", $0);
    split($0,a,"\t");
    if(length(a[1])&&length(a[2])&&length(a[3])) print a[1],a[2],a[3];
  }' tsv/ulp_panel.tsv > "$PANEL_TMP"

panel_stream(){ awk -F"\t" 'NF>=3{printf("%s %s %s\n",$1,$2,$3)}' "$PANEL_TMP"; }

# headers
echo -e "name\tDmax\ty\tsigma\tr0\tr1\tr2\tr3\tr4\tresidual\tz\tk\tmaxQ\tBIC\tbucketN\tstab\torbit\tmults" > "$BEST_TSV"
echo -e "name\tDmax\tr0\tr1\tr2\tr3\tr4\teps\tz\tk\tmaxQ\tBIC" > "$BUCKET_TSV"

RESLIST=()

while read -r nm y s; do
  [ -z "${nm:-}" ] && continue
  for D in "${DENOMS[@]}"; do
    MAP="$(
      awk -v Y0="$y" -v SIG0="$s" -v DMAX0="$D" -v PMAX0="$P_MAX" -v MDL0="$MDL_LAMBDA" \
          -v Z0v="$ln_alpha" -v Z1v="$ln_alphas" -v Z2v="$ln_pi" -v Z3v="$ln_phi" -v Z4v="$ln_mpme" \
          -f "$AWK_SEARCH_FILE" </dev/null || true
    )"
    [ -z "$MAP" ] && continue
    rep="$(printf "%s\n" "$MAP" | awk -F'\t' '$1=="REP"{print; exit}')"
    [ -z "$rep" ] && continue
    IFS=$'\t' read -r _ r0 r1 r2 r3 r4 eps z k maxQ bestB bucketN <<< "$rep"

    # orbit / stabilizer
    read -r stab orbit mults < <(
      awk -v a="$r0" -v b="$r1" -v c="$r2" -v d="$r3" -v e="$r4" '
        function ab(x){return x<0?-x:x}
        function key(x){return sprintf("%.12f",x)}
        function fact(n, i,f){f=1; for(i=2;i<=n;i++) f*=i; return f}
        BEGIN{
          v[1]=ab(a); v[2]=ab(b); v[3]=ab(c); v[4]=ab(d); v[5]=ab(e);
          zc=0; for(i=1;i<=5;i++) if(v[i]==0) zc++;
          for(i=1;i<=5;i++){ if(v[i]==0) continue; cnt[key(v[i])]++ }
          stab=1; for(i=1;i<=zc;i++) stab*=2;
          mult=""; for (k in cnt){ stab*=fact(cnt[k]); mult=mult sprintf("%s:%d,",k,cnt[k]) }
          if(length(mult)>0) sub(/,$/,"",mult);
          orbit=int(3840/(stab>0?stab:1));
          print stab, orbit, mult;
        }')
    printf "%s\t%d\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.12g\t%.6g\t%d\t%d\t%.6f\t%d\t%s\t%s\t%s\n" \
      "$nm" "$D" "$y" "$s" "$r0" "$r1" "$r2" "$r3" "$r4" "$eps" "$z" "$k" "$maxQ" "$bestB" "$bucketN" "$stab" "$orbit" "$mults" \
      >> "$BEST_TSV"

    printf "%s\n" "$MAP" | awk -v nm="$nm" -v D="$D" -F'\t' '
      BEGIN{OFS="\t"}
      $1=="BUCKET"{printf "%s\t%d\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", nm, D, $2,$3,$4,$5,$6,$7,$8,$9,$10,$11}
    ' >> "$BUCKET_TSV"

    [ "$D" -eq 12 ] && RESLIST+=("$eps")
  done
done < <(panel_stream)

# κ (D=12 reps) with simple bootstrap CI
if [ "${#RESLIST[@]}" -ge 2 ]; then
  awk -v B=5000 -v seed=42 '
    function kappa(arr,n,   I1,I2,i){I1=0;I2=0;for(i=1;i<=n;i++){I1+=arr[i]^2; I2+=arr[i]^4}
      return (I1>0? 5*(I2/(I1*I1)) - 3 : 0/0) }
    BEGIN{
      n=ARGC-1; srand(seed); for(i=1;i<=n;i++) e[i]=ARGV[i]+0
      k0=kappa(e,n)
      m=B; for(b=1;b<=m;b++){ for(i=1;i<=n;i++){ j=int(1+rand()*n); eb[i]=e[j] } K[b]=kappa(eb,n) }
      for(i=1;i<=m;i++) for(j=i+1;j<=m;j++) if(K[j]<K[i]){ t=K[i]; K[i]=K[j]; K[j]=t }
      lo=K[int(0.16*m)]; hi=K[int(0.84*m)]
      printf("kappa (D=12 reps) = %.6g   n = %d   68%% CI = [%.6g, %.6g]\n", k0, n, lo, hi)
    }' "${RESLIST[@]}" > "$KAPPA_TXT"
else
  echo "kappa: NA (no residuals)" > "$KAPPA_TXT"
fi

echo "OK: wrote $BEST_TSV, $BUCKET_TSV, $KAPPA_TXT"
