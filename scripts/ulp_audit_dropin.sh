#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
export LC_NUMERIC=C

mkdir -p tsv

OUT_FITS="tsv/ulp_audit_fits.tsv"
OUT_ALPHA="tsv/ulp_audit_codataa.tsv"

# ---- Inputs (you can keep fractions like 1/137... or decimals) ----
alpha='1/137.035999084'        # CODATA 2022 central
alphas='0.1179'                 # PDG @ M_Z
pi_val='3.141592653589793'
phi_val='1.6180339887498948'
mp_me='1836.15267343'           # PDG

# ---- Robust: turn "a/b" or decimal into ln(value)
fraclog() {
  # $1 = string, may be "a/b" or decimal
  awk -v x="$1" 'BEGIN{
    if (x ~ /^[[:space:]]*[0-9.]+[[:space:]]*\/[[:space:]]*[0-9.]+[[:space:]]*$/) {
      split(x,t,"/");
      v=(t[1]+0)/(t[2]+0);
    } else {
      v = x+0;
    }
    if (!(v>0)) { print "0"; exit }   # guard; caller provides physics, so v>0
    printf("%.12f", log(v)+0.0);
  }'
}

ln_alpha="$(fraclog "$alpha")"
ln_alphas="$(fraclog "$alphas")"
ln_pi="$(fraclog "$pi_val")"
ln_phi="$(fraclog "$phi_val")"
ln_mpme="$(fraclog "$mp_me")"

# Show basis actually used (stderr)
{
  echo "Z basis (derived):"
  echo "  ln_alpha=${ln_alpha}"
  echo "  ln_alphas=${ln_alphas}"
  echo "  ln_pi=${ln_pi}"
  echo "  ln_phi=${ln_phi}"
  echo "  ln_mp/me=${ln_mpme}"
} 1>&2

# ---- Targets (placeholders; replace with your attested central ±1σ)
ln_sin_theta12='-1.49'
ln_OmegaLambda='-0.370'
sigma_ln_alpha='1e-12'
sigma_ln_alphas='1e-12'
sigma_ln_mpme='1e-12'
sigma_ln_sin_theta12='0.01'
sigma_ln_OmegaLambda="$(awk -v v="$ln_OmegaLambda" 'BEGIN{print 0.01*((v<0)?-v:v)}')"

emit_row () {
  # name  val  sigma  r1 r2 r3 r4 r5  is_basis
  local name="$1" val="$2" sig="$3" r1="$4" r2="$5" r3="$6" r4="$7" r5="$8" isb="$9"
  awk -v a="$ln_alpha" -v b="$ln_alphas" -v c="$ln_pi" -v d="$ln_phi" -v e="$ln_mpme" \
      -v r1="$r1" -v r2="$r2" -v r3="$r3" -v r4="$r4" -v r5="$r5" \
      -v name="$name" -v val="$val" -v sig="$sig" -v isb="$isb" '
    function rf(x, A){ if(x=="0")return 0;
                       if(x~"/"){split(x,A,"/"); return (A[2]==0?0:(A[1]+0)/(A[2]+0))}
                       return x+0 }
    BEGIN{
      zdot = (a+0)*rf(r1) + (b+0)*rf(r2) + (c+0)*rf(r3) + (d+0)*rf(r4) + (e+0)*rf(r5)
      res  = (val+0) - zdot
      s    = (sig+0); if (s<=0) s=1e-12
      z    = res/s
      printf "%s\t%.12g\t%.12g\t[%s,%s,%s,%s,%s]\t%.12g\t%.12g\t%.6g\t%d\n",
             name, val, sig, r1,r2,r3,r4,r5, zdot, res, z, isb
    }'
}

orbit_calc () {
  awk -v r1="$1" -v r2="$2" -v r3="$3" -v r4="$4" -v r5="$5" '
    function rf(x, A){ if(x=="0")return 0;
                       if(x~"/"){split(x,A,"/"); return (A[2]==0?0:(A[1]+0)/(A[2]+0))}
                       return x+0 }
    function absv(x){ return x<0?-x:x }
    function keyf(x){ return sprintf("%.12f", x) }
    function two_pow(n,  i,p){ p=1; for(i=1;i<=n;i++) p*=2; return p }
    function fact(n,  i,f){ f=1; for(i=2;i<=n;i++) f*=i; return f }
    BEGIN{
      v[1]=absv(rf(r1)); v[2]=absv(rf(r2)); v[3]=absv(rf(r3)); v[4]=absv(rf(r4)); v[5]=absv(rf(r5));
      z=0; for(i=1;i<=5;i++) if(v[i]==0) z++
      for(i=1;i<=5;i++){ if(v[i]==0)continue; k=keyf(v[i]); cnt[k]++ }
      stab=two_pow(z); mults=""
      for(k in cnt){ m=cnt[k]; stab*=fact(m); mults=mults sprintf("%s:%d,",k,m) }
      if(length(mults)>0) sub(/,$/,"",mults)
      orbit=int(3840/(stab>0?stab:1))
      print stab, orbit, mults
    }'
}

# ---- Write TSVs
{
  echo -e "observable\tvalue\tSigma\tr_vector\tZdot\tresidual\tz_score\tis_basis\tstab\torbit\tmultiplicities"

  # basis (trivial fits)
  emit_row ln_alpha    "$ln_alpha"  "$sigma_ln_alpha"   "1/1" "0"   "0"   "0"   "0"   1 | tee /tmp/u_line.tsv >/dev/null
  read -r s o m < <(orbit_calc "1/1" "0" "0" "0" "0"); paste /tmp/u_line.tsv <(printf "%s\t%s\t%s\n" "$s" "$o" "1.000000000000:1")

  emit_row ln_alpha_s  "$ln_alphas" "$sigma_ln_alphas"  "0"   "1/1" "0"   "0"   "0"   1 | tee /tmp/u_line.tsv >/dev/null
  read -r s o m < <(orbit_calc "0" "1/1" "0" "0" "0"); paste /tmp/u_line.tsv <(printf "%s\t%s\t%s\n" "$s" "$o" "1.000000000000:1")

  emit_row ln_mpratio  "$ln_mpme"   "$sigma_ln_mpme"    "0"   "0"   "0"   "0"   "1/1" 1 | tee /tmp/u_line.tsv >/dev/null
  read -r s o m < <(orbit_calc "0" "0" "0" "0" "1/1"); paste /tmp/u_line.tsv <(printf "%s\t%s\t%s\n" "$s" "$o" "1.000000000000:1")

  # non-basis demos (keep as given)
  emit_row ln_sin_theta12 "$ln_sin_theta12" "$sigma_ln_sin_theta12"  "1/12" "-1/12" "0" "0" "-1/6" 0 | tee /tmp/u_line.tsv >/dev/null
  read -r s o m < <(orbit_calc "1/12" "-1/12" "0" "0" "-1/6"); paste /tmp/u_line.tsv <(printf "%s\t%s\t%s\n" "$s" "$o" "0.083333333333:2,0.166666666667:1")

  emit_row ln_OmegaLambda "$ln_OmegaLambda" "$sigma_ln_OmegaLambda"  "0" "1/4" "1/4" "-1/4" "0" 0 | tee /tmp/u_line.tsv >/dev/null
  read -r s o m < <(orbit_calc "0" "1/4" "1/4" "-1/4" "0"); paste /tmp/u_line.tsv <(printf "%s\t%s\t%s\n" "$s" "$o" "0.250000000000:3")
} > "$OUT_FITS"

{
  echo -e "release\talpha\tln_alpha\tbest_r\tZdot\tresidual"
  awk 'BEGIN{
    a2014=1/137.035999139; a2018=1/137.035999084; a2022=1/137.035999084;
    rel[1]="2014"; A[1]=a2014; rel[2]="2018"; A[2]=a2018; rel[3]="2022"; A[3]=a2022;
    for(i=1;i<=3;i++){ lna=log(A[i]); z=lna; printf "%s\t%.12g\t%.9g\t[%s]\t%.9g\t%.3g\n", rel[i], A[i], lna, "1/1,0,0,0,0", z, (lna-z) }
  }'
} > "$OUT_ALPHA"

echo "OK: wrote $OUT_FITS and $OUT_ALPHA"
