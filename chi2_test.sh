#!/usr/bin/env bash
# chi2_test.sh — χ² fit for (c1, c3) unifying arithmetic and spectral invariants
set -euo pipefail

# configurable roots (override via env)
ARITH_DIR="${ARITH_DIR:-./receipts/qcro/taylor_coefficients}"
SPEC_DIR="${SPEC_DIR:-./receipts/monogon/fh_constants}"
OUTPUT_DIR="${OUTPUT_DIR:-./results/chi2_fit}"
VERBOSE="${VERBOSE:-1}"

mkdir -p "$OUTPUT_DIR"

log(){ [ "${VERBOSE}" -ge 1 ] && printf '%s\n' "$*"; }
die(){ printf 'ERROR: %s\n' "$*" >&2; exit 1; }
need(){ command -v "$1" >/dev/null 2>&1 || die "missing dependency: $1"; }

need jq
need awk

FIT_LOG="$OUTPUT_DIR/fit.log"
: > "$FIT_LOG"

log "=== χ² test: arithmetic–spectral matching ===" | tee -a "$FIT_LOG"
log "arithmetic receipts: $ARITH_DIR" | tee -a "$FIT_LOG"
log "spectral receipts:   $SPEC_DIR"   | tee -a "$FIT_LOG"
log "" | tee -a "$FIT_LOG"
# ingest arithmetic: lines -> curve A1 A3 sigma_A1 sigma_A3 cov_A1_A3
ARITH_DATA="$OUTPUT_DIR/arithmetic.dat"; : > "$ARITH_DATA"
shopt -s nullglob
arith_files=("$ARITH_DIR"/*.json)
[ "${#arith_files[@]}" -gt 0 ] || die "no arithmetic JSON receipts in $ARITH_DIR"

for f in "${arith_files[@]}"; do
  curve=$(jq -er '.curve' "$f") || die "curve missing in $f"
  A1=$(jq -er '.A1' "$f") || die "A1 missing in $f"
  A3=$(jq -er '.A3' "$f") || die "A3 missing in $f"
  sA1=$(jq -er '.sigma_A1' "$f") || die "sigma_A1 missing in $f"
  sA3=$(jq -er '.sigma_A3' "$f") || die "sigma_A3 missing in $f"
  covA13=$(jq -er '.cov_A1_A3 // 0' "$f")
  printf '%s %.17g %.17g %.17g %.17g %.17g\n' "$curve" "$A1" "$A3" "$sA1" "$sA3" "$covA13" >> "$ARITH_DATA"
done

n_curves=$(wc -l < "$ARITH_DATA" | awk '{print $1}')
[ "$n_curves" -gt 0 ] || die "no usable arithmetic rows"
# ingest spectral: epsilon_abs, sigma_epsilon, Xi, sigma_Xi, cov_epsilon_Xi
spec_files=("$SPEC_DIR"/*.json)
[ "${#spec_files[@]}" -gt 0 ] || die "no spectral JSON receipts in $SPEC_DIR"
spec_json="${spec_files[0]}"

eps=$(jq -er '.epsilon_abs' "$spec_json")      || die "epsilon_abs missing"
seps=$(jq -er '.sigma_epsilon' "$spec_json")   || die "sigma_epsilon missing"
Xi=$(jq -er '.Xi' "$spec_json")                || die "Xi missing"
sXi=$(jq -er '.sigma_Xi' "$spec_json")         || die "sigma_Xi missing"
cov_eXi=$(jq -er '.cov_epsilon_Xi // 0' "$spec_json")

# invariants
u1=$(awk -v e="$eps" 'BEGIN{printf("%.17g", e*e)}')
u3="$Xi"

log "spectral invariants:" | tee -a "$FIT_LOG"
log "  ε = $eps ± $seps"            | tee -a "$FIT_LOG"
log "  ε² = $u1"                    | tee -a "$FIT_LOG"
log "  Ξ  = $u3 ± $sXi"             | tee -a "$FIT_LOG"
log "  Cov(ε,Ξ) = $cov_eXi"         | tee -a "$FIT_LOG"
log ""                              | tee -a "$FIT_LOG"

# prior for Σ construction; we will recompute at fitted values
c1_prior=1.0
c3_prior=1.0

# accumulators
F11=0; F12=0; F22=0
g1=0;  g2=0
chi2_prior=0
n_used=0

RESID_PRIOR="$OUTPUT_DIR/residuals_prior.dat"
printf '# curve A1 A3 c1u1 c3u3 r1 r3 chi2_contrib\n' > "$RESID_PRIOR"
# loop curves, build Σ using variance propagation, accumulate Fisher and prior χ²
while read -r curve A1 A3 sA1 sA3 covA13; do
  # Σ_11 = sA1^2 + (2 c1 ε)^2 seps^2
  # Σ_22 = sA3^2 + (c3)^2 sXi^2
  # Σ_12 = cov(A1,A3) - (2 c1 ε)(c3) cov(ε,Ξ)
  read -r v11 v22 s12 det Sinv11 Sinv12 Sinv22 <<EOF
$(awk -v sA1="$sA1" -v sA3="$sA3" -v c1="$c1_prior" -v c3="$c3_prior" \
     -v eps="$eps" -v seps="$seps" -v sXi="$sXi" -v cov_eXi="$cov_eXi" '
BEGIN{
  v11 = sA1*sA1 + (2*c1*eps)*(2*c1*eps)*seps*seps;
  v22 = sA3*sA3 + (c3*c3)*sXi*sXi;
  s12 = (cov_eXi==0)? 0 : ( -2*c1*eps*c3*cov_eXi );
  det = v11*v22 - s12*s12;
  if(det<=0){printf("nan nan nan nan 0 0 0\n"); exit}
  Sinv11 = v22/det; Sinv22 = v11/det; Sinv12 = -s12/det;
  printf("%.17g %.17g %.17g %.17g %.17g %.17g %.17g\n", v11, v22, s12, det, Sinv11, Sinv12, Sinv22);
}')
EOF
  [ "$det" = "nan" ] && { log "skip $curve: singular Σ"; continue; }

  # design X = diag(u1, u3)
  F11=$(awk -v F11="$F11" -v u1="$u1" -v S11="$Sinv11" 'BEGIN{printf("%.17g", F11 + u1*u1*S11)}')
  F12=$(awk -v F12="$F12" -v u1="$u1" -v u3="$u3" -v S12="$Sinv12" 'BEGIN{printf("%.17g", F12 + u1*u3*S12)}')
  F22=$(awk -v F22="$F22" -v u3="$u3" -v S22="$Sinv22" 'BEGIN{printf("%.17g", F22 + u3*u3*S22)}')

  g1=$(awk -v g1="$g1" -v u1="$u1" -v S11="$Sinv11" -v S12="$Sinv12" -v A1="$A1" -v A3="$A3" \
        'BEGIN{printf("%.17g", g1 + u1*(S11*A1 + S12*A3))}')
  g2=$(awk -v g2="$g2" -v u3="$u3" -v S12="$Sinv12" -v S22="$Sinv22" -v A1="$A1" -v A3="$A3" \
        'BEGIN{printf("%.17g", g2 + u3*(S12*A1 + S22*A3))}')

  r1=$(awk -v A1="$A1" -v c1="$c1_prior" -v u1="$u1" 'BEGIN{printf("%.17g", A1 - c1*u1)}')
  r3=$(awk -v A3="$A3" -v c3="$c3_prior" -v u3="$u3" 'BEGIN{printf("%.17g", A3 - c3*u3)}')
  chi=$(awk -v r1="$r1" -v r3="$r3" -v S11="$Sinv11" -v S12="$Sinv12" -v S22="$Sinv22" \
         'BEGIN{printf("%.17g", r1*r1*S11 + 2*r1*r3*S12 + r3*r3*S22)}')
  chi2_prior=$(awk -v c="$chi2_prior" -v d="$chi" 'BEGIN{printf("%.17g", c+d)}')

  printf '%s %.17g %.17g %.17g %.17g %.17g %.17g %.17g\n' \
         "$curve" "$A1" "$A3" "$(awk -v c1="$c1_prior" -v u1="$u1" 'BEGIN{printf("%.17g", c1*u1)}')" \
         "$(awk -v c3="$c3_prior" -v u3="$u3" 'BEGIN{printf("%.17g", c3*u3)}')" \
         "$r1" "$r3" "$chi" >> "$RESID_PRIOR"

  n_used=$((n_used+1))
done < "$ARITH_DATA"

[ "$n_used" -gt 0 ] || die "no curves usable after Σ check"
# solve Fisher system
detF=$(awk -v F11="$F11" -v F22="$F22" -v F12="$F12" 'BEGIN{printf("%.17g", F11*F22 - F12*F12)}')
[ "$(awk -v d="$detF" 'BEGIN{print (d<=0)}')" -eq 0 ] || die "singular Fisher matrix"

c1_fit=$(awk -v F22="$F22" -v F12="$F12" -v g1="$g1" -v g2="$g2" -v det="$detF" 'BEGIN{printf("%.17g", (F22*g1 - F12*g2)/det)}')
c3_fit=$(awk -v F11="$F11" -v F12="$F12" -v g1="$g1" -v g2="$g2" -v det="$detF" 'BEGIN{printf("%.17g", (F11*g2 - F12*g1)/det)}')

Delta_c1=$(awk -v F11="$F11" -v F22="$F22" -v det="$detF" 'BEGIN{printf("%.17g", sqrt(F22/det))}')
Delta_c3=$(awk -v F11="$F11" -v F22="$F22" -v det="$detF" 'BEGIN{printf("%.17g", sqrt(F11/det))}')

log "fit (first pass):" | tee -a "$FIT_LOG"
log "  c1 = $c1_fit ± $Delta_c1" | tee -a "$FIT_LOG"
log "  c3 = $c3_fit ± $Delta_c3" | tee -a "$FIT_LOG"
# recompute χ² with Σ evaluated at (c1_fit, c3_fit)
chi2_fit=0
RESID_FILE="$OUTPUT_DIR/residuals.dat"
printf '# curve  A1  A3  c1u1  c3u3  r1  r3  chi2_contrib\n' > "$RESID_FILE"

while read -r curve A1 A3 sA1 sA3 covA13; do
  read -r det Sinv11 Sinv12 Sinv22 r1 r3 chi c1u1 c3u3 <<EOF
$(awk -v A1="$A1" -v A3="$A3" -v sA1="$sA1" -v sA3="$sA3" -v covA="$covA13" \
     -v c1="$c1_fit" -v c3="$c3_fit" -v eps="$eps" -v seps="$seps" -v sXi="$sXi" -v cov_eXi="$cov_eXi" \
     -v u1="$u1" -v u3="$u3" '
BEGIN{
  v11 = sA1*sA1 + (2*c1*eps)*(2*c1*eps)*seps*seps;
  v22 = sA3*sA3 + (c3*c3)*sXi*sXi;
  s12 = covA - 2*c1*eps*c3*cov_eXi;
  det = v11*v22 - s12*s12; if(det<=0){print "nan 0 0 0 0 0 0 0 0"; exit}
  Sinv11 = v22/det; Sinv22 = v11/det; Sinv12 = -s12/det;
  r1 = A1 - c1*u1; r3 = A3 - c3*u3;
  chi = r1*r1*Sinv11 + 2*r1*r3*Sinv12 + r3*r3*Sinv22;
  printf("%.17g %.17g %.17g %.17g %.17g %.17g %.17g %.17g %.17g\n", det, Sinv11, Sinv12, Sinv22, r1, r3, chi, c1*u1, c3*u3);
}')
EOF
  [ "$det" = "nan" ] && { log "skip $curve at fit Σ: singular"; continue; }
  chi2_fit=$(awk -v a="$chi2_fit" -v b="$chi" 'BEGIN{printf("%.17g", a+b)}')
  printf '%s %.17g %.17g %.17g %.17g %.17g %.17g %.17g\n' "$curve" "$A1" "$A3" "$c1u1" "$c3u3" "$r1" "$r3" "$chi" >> "$RESID_FILE"
done < "$ARITH_DATA"

dof=$((2*n_used - 2))
chi2_dof=$(awk -v c="$chi2_fit" -v d="$dof" 'BEGIN{printf("%.17g", c/d)}')

{
  echo ""
  echo "=== results ==="
  echo "curves used: $n_used"
  echo "degrees of freedom: $dof"
  echo "c1 = $c1_fit ± $Delta_c1"
  echo "c3 = $c3_fit ± $Delta_c3"
  echo "χ² = $chi2_fit"
  echo "χ²/dof = $chi2_dof"
} | tee -a "$FIT_LOG"

verdict=$(awk -v q="$chi2_dof" 'BEGIN{
  if(q<0.5)      print "error model too conservative (χ²/dof < 0.5)";
  else if(q>3.0) print "systematic deviation (χ²/dof > 3)";
  else           print "consistent with flat isomorphism";
}')
echo "verdict: $verdict" | tee -a "$FIT_LOG"

c1_z=$(awk -v m="$c1_fit" -v s="$Delta_c1" 'BEGIN{printf("%.17g", (m-1)/s)}')
c3_z=$(awk -v m="$c3_fit" -v s="$Delta_c3" 'BEGIN{printf("%.17g", (m-1)/s)}')
echo "z-scores vs canonical gauge: (c1-1)/Δc1=$c1_z, (c3-1)/Δc3=$c3_z" | tee -a "$FIT_LOG"

echo "residuals → $RESID_FILE" | tee -a "$FIT_LOG"
echo "log       → $FIT_LOG"     | tee -a "$FIT_LOG"

# optional plot if gnuplot present
if command -v gnuplot >/dev/null 2>&1; then
  PGP="$OUTPUT_DIR/plot_residuals.gp"
  cat > "$PGP" <<'GP'
set terminal png size 900,580
set output 'residuals.png'
set title 'Residuals per curve'
set xlabel 'curve index'
set ylabel 'residual'
set grid
plot 'residuals.dat' using 0:6 with points pt 7 ps 1.2 title 'r1 = A1 - c1·ε²', \
     '' using 0:7 with points pt 9 ps 1.2 title 'r3 = A3 - c3·Ξ'
GP
  (cd "$OUTPUT_DIR" && gnuplot "$(basename "$PGP")" >/dev/null 2>&1 || true)
  echo "plot       → $OUTPUT_DIR/residuals.png" | tee -a "$FIT_LOG"
fi

exit 0
