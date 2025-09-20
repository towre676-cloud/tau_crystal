#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
OUT_DIR="analysis/morpho/ref"; MAN="$OUT_DIR/cohort_manifest.tsv"; COMB="$OUT_DIR/cohort_combined.tsv"
: > "$MAN"; : > "$COMB"
printf "%s\n" "dataset_name\tlandmark_count\tsubject_count\tdim\tlicense\tid\thash" >> "$MAN"
while IFS=$'\t' read -r DID DNAME DLIC DPATH DSTAT; do
  [ "$DID" = "id" ] && continue
  case "$DPATH" in "<PUT/"*|"" ) echo "skipping $DID (path not set)"; continue ;; esac
  [ -f "$DPATH" ] || { echo "missing $DPATH for $DID"; continue; }
  H=$(sha256sum "$DPATH" | awk "{print $1}")
  C=$(awk "NR==1{print NF}" "$DPATH")
  N=$(( (C-1)/3 ))
  awk -v N="$N" 'BEGIN{OFS="\t"} {id=$1;sx=sy=sz=0;for(i=1;i<=N;i++){x[i]=$(3*(i-1)+2);y[i]=$(3*(i-1)+3);z[i]=$(3*(i-1)+4);sx+=x[i];sy+=y[i];sz+=z[i]}cx=sx/N;cy=sy/N;cz=sz/N;r2=0;for(i=1;i<=N;i++){x[i]-=cx;y[i]-=cy;z[i]-=cz;r2+=x[i]*x[i]+y[i]*y[i]+z[i]*z[i]}r=sqrt(r2);if(r==0)r=1;printf "%s",id;for(i=1;i<=N;i++){printf OFS "%.8f",x[i]/r;printf OFS "%.8f",y[i]/r;printf OFS "%.8f",z[i]/r}printf "\n"}' "$DPATH" >> "$COMB"
  SUBJ=$(wc -l < "$DPATH" | awk "{print $1}")
  printf "%s\n" "$DNAME\t"N"\t"$SUBJ"\t3D\t"$DLIC"\t"$DID"\t"$H >> "$MAN"
done < "analysis/morpho/ref/datasets.registry.tsv"
echo "ingested → $COMB"; echo "manifest → $MAN"
