#!/usr/bin/env bash
set +H
umask 022
IN="validation/input"
OUT="analysis/validation/face_stats.tsv"
mkdir -p analysis/validation
: > "$OUT"
printf "face_id\tsha256\tlines\tok_68\tmin_x\tmax_x\tmean_x\tmin_y\tmax_y\tmean_y\tmin_z\tmax_z\tmean_z\n" >> "$OUT"
find "$IN" -maxdepth 1 -type f -name "*.tsv" | sort | while IFS= read -r F; do
  B=$(basename "$F"); ID=${B%.*}
  SHA=$(sha256sum "$F" 2>/dev/null | awk "{print \$1}")
  LINES=$(wc -l < "$F" 2>/dev/null | tr -d " ")
  OK=$([ "$LINES" -eq 68 ] && printf yes || printf no)
  awk -v ID="$ID" -v SHA="$SHA" -v LINES="$LINES" -v OK="$OK" '{ sub(/\r$/,""); if(NF!=3) next;
    x+=$1; y+=$2; z+=$3;
    if(NR==1){minx=$1;maxx=$1;miny=$2;maxy=$2;minz=$3;maxz=$3}
    if($1<minx)minx=$1; if($1>maxx)maxx=$1;
    if($2<miny)miny=$2; if($2>maxy)maxy=$2;
    if($3<minz)minz=$3; if($3>maxz)maxz=$3
  } END {
    if(NR>0){
      printf "%s\t%s\t%d\t%s\t%.6f\t%.6f\t%.6f\t%.6f\t%.6f\t%.6f\t%.6f\t%.6f\t%.6f\n",
             ID,SHA,LINES,OK,minx,maxx,(x/NR),miny,maxy,(y/NR),minz,maxz,(z/NR);
    }
  }' "$F" >> "$OUT"
done
awk '{ sub(/\r$/,""); print }' "$OUT" > "$OUT.tmp" && mv "$OUT.tmp" "$OUT"
echo "wrote $OUT"
