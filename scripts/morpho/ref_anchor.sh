#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
OUT_DIR="analysis/morpho/ref"; MEAN="$OUT_DIR/cohort_mean.tsv"; VAR="$OUT_DIR/cohort_var_diag.tsv"; SIG="$OUT_DIR/cohort.signature.tsv"
FACE="${1:-}"
[ -f "$FACE" ] || { echo "usage: $0 path/to/face.tsv" >&2; exit 2; }
[ -f "$MEAN" ] && [ -f "$VAR" ] && [ -f "$SIG" ] || { echo "missing cohort stats/signature"; exit 3; }
COLS=$(awk "NR==1{print NF}" "$MEAN")
awk -v C="$COLS" -v M="$MEAN" -v V="$VAR" 'BEGIN{FS=OFS="\t"} NR==FNR{for(j=2;j<=C;j++) mean[j]=$j; next} NR==FNR+1{for(j=2;j<=C;j++) var[j]=$j; next} NR>FNR+1{ s2=0; for(j=2;j<=C;j++){x=$j; m=mean[j]; v=var[j]; if(v<=0) v=1e-9; z=(x-m)/sqrt(v); s2+=z*z} D=sqrt(s2) } END{printf "MAHALANOBIS=%.6f\n", D}' "$MEAN" "$VAR" "$FACE"
HSIG=$(awk '/^SIG_SHA256/{print $2}' "$SIG")
printf "%s\n" "REF_SIG=sha256:$HSIG"
