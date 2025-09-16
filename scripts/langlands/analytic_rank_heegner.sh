#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

LAUR="analysis/laurent_ring.tsv"            # cols: re  im  K_k  q  seed
OUT_TSV="analysis/analytic_heegner.tsv"
OUT_JSON="analysis/analytic_heegner_receipt.json"
OUT_SHA="analysis/analytic_heegner.sha256"
NEXT_HEX="analysis/next_nonce_from_heegner.hex"

# Tunables (env can override)
DELTAS="${RANK_DELTAS:-0.01 0.02 0.05}"
TAU_L0="${RANK_TAU_L0:-1e-3}"
TAU_SLOPE="${RANK_TAU_SLOPE:-1e-2}"
TAU_LP="${RANK_TAU_LP:-1e-6}"
PANEL="${RANK_PANEL:-2 3 5 7 11 13 17}"

[ -s "$LAUR" ] || { echo "[rank] missing $LAUR"; exit 1; }
[ -f "$OUT_TSV" ] || printf "phi\tL0\tLprime_proxy\tOmega_proxy\tHeight_proxy\tdeltas\tsign_changes\tslope_avg\tcurve_avg\trank_guess\n" > "$OUT_TSV"

awk -v deltas="$DELTAS" -v panel="$PANEL" -v out_tsv="$OUT_TSV" -v out_json="$OUT_JSON" \
    -v tauL0="$TAU_L0" -v tauSlope="$TAU_SLOPE" -v tauLp="$TAU_LP" '
{ re=$1+0; im=$2+0; Kk=$3+0 }  # last row wins
END{
  if (re!=re || im!=im) { re=1; im=0 }             # NaN guard
  phi = atan2(im,re)
  if (!(Kk==Kk) || Kk<=1e-18) Kk=1e-18             # period guard

  nP = split(panel,P," ")
  # central value L0 = Σ cos(pφ)/p^{1/2}
  L0=0
  for(i=1;i<=nP;i++){ p=P[i]+0; L0 += cos(p*phi)/exp(0.5*log(p)) }

  # L′ proxy: 4Σ cos(pφ)*log(√p)
  Lp=0
  for(i=1;i<=nP;i++){ p=P[i]+0; Lp += 4.0*cos(p*phi)*(0.5*log(p)) }

  dN = split(deltas,D," ")
  sign_changes=0; slope_acc=0; curve_acc=0; tested=0
  for(j=1;j<=dN;j++){
    d=D[j]+0
    Lplus=0; Lminus=0
    for(i=1;i<=nP;i++){
      p=P[i]+0; c=cos(p*phi)
      Lplus  += c / exp((0.5+d)*log(p))
      Lminus += c / exp((0.5-d)*log(p))
    }
    if (Lplus*Lminus < 0) sign_changes++
    slope = (Lminus - Lplus)/(2.0*d); if(slope<0)slope=-slope
    curve = (Lplus + Lminus - 2.0*L0)/(d*d); if(curve<0)curve=-curve
    slope_acc += slope; curve_acc += curve; tested++
  }
  slope_avg = (tested? slope_acc/tested : 0)
  curve_avg = (tested? curve_acc/tested : 0)

  Height = (L0*L0)/Kk
  absL0=(L0<0?-L0:L0); absLp=(Lp<0?-Lp:Lp)
  rank_guess = (sign_changes>=1 ? 1 : ((absL0<tauL0 && slope_avg<tauSlope && absLp<tauLp)?2:1))

  # TSV row
  printf("%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t", phi,L0,Lp,Kk,Height) >> out_tsv
  printf("%s\t%d\t%.16g\t%.16g\t%d\n", deltas,sign_changes,slope_avg,curve_avg,rank_guess) >> out_tsv

  # JSON (stable key order)
  pass=(rank_guess>=2)?"true":"false"
  printf("{") > out_json
  printf("\"schema\":\"taucrystal/analytic_heegner/v3\",") >> out_json
  printf("\"phi\":%.16g,",phi) >> out_json
  printf("\"L0\":%.16g,",L0) >> out_json
  printf("\"Lprime_proxy\":%.16g,",Lp) >> out_json
  printf("\"Omega_proxy\":%.16g,",Kk) >> out_json
  printf("\"height_proxy\":%.16g,",Height) >> out_json
  printf("\"deltas\":\"%s\",",deltas) >> out_json
  printf("\"sign_changes\":%d,",sign_changes) >> out_json
  printf("\"slope_avg\":%.16g,",slope_avg) >> out_json
  printf("\"curve_avg\":%.16g,",curve_avg) >> out_json
  printf("\"rank_guess\":%d,",rank_guess) >> out_json
  printf("\"pass\":%s",pass) >> out_json
  printf("}\n") >> out_json
}
' "$LAUR"

# hash -> next-nonce seed
sha256sum "$OUT_TSV" | awk '{print $1}' > "$OUT_SHA"
cut -c1-64 "$OUT_SHA" > "$NEXT_HEX"

# exit 0 only if rank ≥ 2 (double-zero proxy)
R=$(tail -n1 "$OUT_TSV" | awk -F'\t' '{print $10+0}')
[ "$R" -ge 2 ] && exit 0 || exit 1
