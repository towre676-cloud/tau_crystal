#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
OUT_DIR="analysis/morpho/ref"
COMB="$OUT_DIR/cohort_combined.tsv"
MEAN="$OUT_DIR/cohort_mean.tsv"
VAR="$OUT_DIR/cohort_var_diag.tsv"
SIG="$OUT_DIR/cohort.signature.tsv"
[ -f "$COMB" ] || { echo "missing $COMB (run ref_ingest.sh)"; exit 2; }
COLS=$(awk "NR==1{print NF}" "$COMB")
NROW=$(wc -l < "$COMB" | awk "{print $1}")
: > "$MEAN"; : > "$VAR"
awk -v C="$COLS" '{for(j=2;j<=C;j++){s[j]+=$j}} END{for(j=2;j<=C;j++){m[j]=s[j]/NR; if(j==2) printf "id"; printf "\t" m[j]} printf "\n"}' "$COMB" >> "$MEAN"
awk -v C="$COLS" -v M="$MEAN" 'BEGIN{FS=OFS="\t"} NR==FNR{for(j=2;j<=C;j++) mean[j]=$j; next} {for(j=2;j<=C;j++){d=$j-mean[j]; v[j]+=d*d}} END{for(j=2;j<=C;j++){vv=(NR>1)?v[j]/(NR-1):0; if(j==2) printf "id"; printf OFS "%.10f", vv} printf "\n"}' "$MEAN" "$COMB" >> "$VAR"
HMEAN=$(sha256sum "$MEAN" | awk "{print $1}")
HVAR=$(sha256sum "$VAR" | awk "{print $1}")
: > "$SIG"
printf "%s\n" "ROWS\t$NROW" >> "$SIG"
printf "%s\n" "COLS\t$COLS" >> "$SIG"
printf "%s\n" "MEAN_SHA256\t$HMEAN" >> "$SIG"
printf "%s\n" "VAR_SHA256\t$HVAR" >> "$SIG"
HSIG=$(sha256sum "$SIG" | awk "{print $1}")
printf "%s\n" "SIG_SHA256\t$HSIG" >> "$SIG"
echo "signature → $SIG (sha256=$HSIG)"; echo "mean → $MEAN"; echo "var(diag) → $VAR"
