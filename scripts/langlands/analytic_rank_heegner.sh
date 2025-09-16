#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "$(dirname "$0")/../.." || exit 1

LAUR="analysis/laurent_ring.tsv"                 # last row: re  im  K_k  q  seed
OUT_TSV="analysis/analytic_heegner.tsv"
OUT_JSON="analysis/analytic_heegner_receipt.json"
OUT_SHA="analysis/analytic_heegner.sha256"
NEXT_HEX="analysis/next_nonce_from_heegner.hex"

[ -s "$LAUR" ] || { echo "[rank] missing $LAUR"; exit 1; }

# grab the last Laurent row and compute phi = atan2(im,re)
read -r PHI KQ <<EOF
$(awk 'END{re=$1+0; im=$2+0; Kk=$3+0; q=$4+0; printf "%.16g %.16g %.16g %.16g\n", atan2(im,re), Kk, q, 0}' "$LAUR" | awk '{printf "%s %s\n",$1,$2}')
EOF

# fallbacks (shouldn’t hit if laurent ran)
[ -z "$PHI" ] && PHI=0
[ -z "$KQ"  ] && KQ=1
Kk="$KQ"

# === L′(1/2) proxy from small primes via cos(p*phi) (no external libs) ===
# We use: L′_proxy = 4 * Σ_{p∈P} cos(pφ) * log(√p)  (P = small prime panel)
LPRIME=$(awk -v phi="$PHI" 'BEGIN{
  pi=4*atan2(1,1);
  split("2 3 5 7 11 13 17", P, " ");
  s=0;
  for(i in P){ p=P[i]+0; s+=4.0*cos(p*phi)*(0.5*log(p)); }
  printf "%.16g", s;
}')

# === Period proxy and Heegner height proxy (signal only) ===
# Use K(k) from the Laurent layer as an invariant period proxy.
OMEGA=$(awk -v K="'$Kk'" 'BEGIN{printf "%.16g", (K+0)}')
HEIGHT=$(awk -v Lp="$LPRIME" -v Om="$OMEGA" 'BEGIN{
  if(Om<=1e-18) Om=1e-18;
  printf "%.16g", (Lp*Lp)/Om;
}')

# threshold for “small height” -> rank≥2 signal
EPS="1e-12"
RANK=1; awk -v h="$HEIGHT" -v e="$EPS" 'BEGIN{exit !(h<e)}' && RANK=2

# write TSV (header once), append a deterministic row
if [ ! -f "$OUT_TSV" ]; then
  printf "phi\tLprime_proxy\tOmega_proxy\tHeight_proxy\teps\trank_guess\n" > "$OUT_TSV"
fi
printf "%.16g\t%.16g\t%.16g\t%.16g\t%s\t%d\n" "$PHI" "$LPRIME" "$OMEGA" "$HEIGHT" "$EPS" "$RANK" >> "$OUT_TSV"

# write stable JSON (no jq; fixed key order)
pass=false; [ "$RANK" -ge 2 ] && pass=true
{
  printf '{'
  printf '"schema":"taucrystal/analytic_heegner/v1",'
  printf '"phi":%.16g,', "$PHI"
  printf '"Lprime_proxy":%.16g,', "$LPRIME"
  printf '"Omega_proxy":%.16g,', "$OMEGA"
  printf '"height_proxy":%.16g,', "$HEIGHT"
  printf '"eps":"%s",', "$EPS"
  printf '"rank_guess":%d,', "$RANK"
  printf '"pass":%s', "$pass"
  printf '}\n'
} > "$OUT_JSON"

# hash TSV to make a next-nonce seed (hex)
sha256sum "$OUT_TSV" | awk '{print $1}' > "$OUT_SHA"
cut -c1-64 "$OUT_SHA" > "$NEXT_HEX"

echo "[rank] phi=$(printf %.6g "$PHI") Lp=$(printf %.6g "$LPRIME") H=$(printf %.3e "$HEIGHT") rank~$RANK"
# exit code lets you gate discoveries, but keep non-fatal by default
[ "$RANK" -ge 2 ] && exit 0 || exit 1
