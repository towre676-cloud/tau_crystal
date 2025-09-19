#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

LAUR="analysis/laurent_ring.tsv"            # cols: re  im  K_k  q  seed
OUT_TSV="analysis/analytic_heegner.tsv"
OUT_JSON="analysis/analytic_heegner_receipt.json"
OUT_SHA="analysis/analytic_heegner.sha256"
NEXT_HEX="analysis/next_nonce_from_heegner.hex"

# Tunables (env can override). Default deltas use φ^(-1..3).
DELTAS="${RANK_DELTAS:-0.618034 0.381966 0.236068}"
SCALES="${RANK_SCALES:-1 2 5}"                  # multi-scale analysis (×s/10)
TAU_L0="${RANK_TAU_L0:-1e-3}"
TAU_SLOPE="${RANK_TAU_SLOPE:-1e-2}"
TAU_LP="${RANK_TAU_LP:-1e-6}"
PANEL="${RANK_PANEL:-2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97}"

[ -s "$LAUR" ] || { echo "[rank] missing $LAUR"; exit 1; }
[ -f "$OUT_TSV" ] || printf "phi\tL0\tLprime_proxy\tOmega_proxy\tHeight_proxy\tdeltas\tscales\tsign_changes\tslope_avg\tcurve_avg\tdom_p\tdom_ratio\tfe_consistency\tbsd_log_height\trank_guess\n" > "$OUT_TSV"

awk -v deltas="$DELTAS" -v scales="$SCALES" -v panel="$PANEL" \
    -v out_tsv="$OUT_TSV" -v out_json="$OUT_JSON" \
    -v tauL0="$TAU_L0" -v tauSlope="$TAU_SLOPE" -v tauLp="$TAU_LP" '
{ re=$1+0; im=$2+0; Kk=$3+0 }  # last row wins
END{
  if (re!=re || im!=im) { re=1; im=0 }
  phi = atan2(im,re)
  if (!(Kk==Kk) || Kk<=1e-18) Kk=1e-18

  nP = split(panel,P," ")
  # central contributions at 1/2
  L0=0; absSum=0; domP=0; domAbs=0
  for(i=1;i<=nP;i++){
    p=P[i]+0; c=cos(p*phi)/exp(0.5*log(p))
    L0 += c
    ca=(c<0?-c:c); absSum+=ca
    if(ca>domAbs){ domAbs=ca; domP=p }
  }
  dom_ratio = (absSum>1e-18 ? domAbs/absSum : 0)

  # L′ proxy
  Lp=0
  for(i=1;i<=nP;i++){ p=P[i]+0; Lp += 4.0*cos(p*phi)*(0.5*log(p)) }

  # multi-scale delta analysis
  split(deltas, D, " "); dN=length(D)
  split(scales, S, " ");  sN=length(S)
  total_sign_changes=0; slope_acc=0; curve_acc=0; tested=0; fe_acc=0

  for(ss=1; ss<=sN; ss++){
    dscale=(S[ss]+0)/10.0
    scale_sign_changes=0
    for(j=1; j<=dN; j++){
      d=D[j]*dscale
      Lplus=0; Lminus=0
      for(i=1;i<=nP;i++){
        p=P[i]+0; c=cos(p*phi)
        Lplus  += c / exp((0.5+d)*log(p))
        Lminus += c / exp((0.5-d)*log(p))
      }
      if (Lplus*Lminus < 0) { scale_sign_changes++; total_sign_changes++ }
      slope = (Lminus - Lplus)/(2.0*d); if(slope<0)slope=-slope
      curve = (Lplus + Lminus - 2.0*L0)/(d*d); if(curve<0)curve=-curve
      slope_acc += slope; curve_acc += curve; tested++

      # functional-equation parity check (root number guess)
      w = (Lplus*Lminus<0 ? -1 : +1)
      fe_acc += ((Lplus + w*Lminus) < 0 ? -(Lplus + w*Lminus) : (Lplus + w*Lminus))
    }
    # (optional) could record per-scale sign changes if needed
  }

  slope_avg = (tested? slope_acc/tested : 0)
  curve_avg = (tested? curve_acc/tested : 0)
  fe_cons   = (tested? fe_acc/tested : 0)

  Height = (L0*L0)/Kk
  absL0=(L0<0?-L0:L0); absLp=(Lp<0?-Lp:Lp)

  # crude BSD: log(|L′|/Ω) (guarded)
  bsd_log_h = 0
  if (absLp<=1e-18) absLp=1e-18
  bsd_log_h = log(absLp/Kk)

  # rank proxy
  rank_guess = (total_sign_changes>=1 ? 1 : ((absL0<tauL0 && slope_avg<tauSlope && absLp<tauLp)?2:1))

  # TSV row
  printf("%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t", phi,L0,Lp,Kk,Height) >> out_tsv
  printf("%s\t%s\t%d\t%.16g\t%.16g\t%d\t%.16g\t%.16g\t%d\n", deltas,scales,total_sign_changes,slope_avg,curve_avg,domP,dom_ratio,fe_cons,rank_guess) >> out_tsv

  # JSON (stable order)
  pass=(rank_guess>=2)?"true":"false"
  printf("{") > out_json
  printf("\"schema\":\"taucrystal/analytic_heegner/v4\",") >> out_json
  printf("\"phi\":%.16g,",phi) >> out_json
  printf("\"L0\":%.16g,",L0) >> out_json
  printf("\"Lprime_proxy\":%.16g,",Lp) >> out_json
  printf("\"Omega_proxy\":%.16g,",Kk) >> out_json
  printf("\"height_proxy\":%.16g,",Height) >> out_json
  printf("\"deltas\":\"%s\",",deltas) >> out_json
  printf("\"scales\":\"%s\",",scales) >> out_json
  printf("\"sign_changes\":%d,",total_sign_changes) >> out_json
  printf("\"slope_avg\":%.16g,",slope_avg) >> out_json
  printf("\"curve_avg\":%.16g,",curve_avg) >> out_json
  printf("\"dominant_prime\":%d,",domP) >> out_json
  printf("\"dom_ratio\":%.16g,",dom_ratio) >> out_json
  printf("\"fe_consistency\":%.16g,",fe_cons) >> out_json
  printf("\"bsd_log_height\":%.16g,",bsd_log_h) >> out_json
  printf("\"tau_L0\":\"%s\",",tauL0) >> out_json
  printf("\"tau_slope\":\"%s\",",tauSlope) >> out_json
  printf("\"tau_Lp\":\"%s\",",tauLp) >> out_json
  printf("\"rank_guess\":%d,",rank_guess) >> out_json
  printf("\"pass\":%s",pass) >> out_json
  printf("}\n") >> out_json
}
' "$LAUR"

sha256sum "$OUT_TSV" | awk '{print $1}' > "$OUT_SHA"
cut -c1-64 "$OUT_SHA" > "$NEXT_HEX"

R=$(tail -n1 "$OUT_TSV" | awk -F'\t' '{print $15+0}')
[ "$R" -ge 2 ] && exit 0 || exit 1
