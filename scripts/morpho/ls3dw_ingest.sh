#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
ROOT="$(cd "$(dirname "$0")/../.."; pwd)"
IN="${1:-}"
OUT="$ROOT/analysis/morpho/output"; IDX="$ROOT/analysis/morpho/index"; LED="$ROOT/.tau_ledger/faces"
[ -n "$IN" ] || { echo "usage: $0 /path/to/LS3D-W-root"; exit 2; }
command -v sha256sum >/dev/null 2>&1 || { echo "sha256sum missing"; exit 3; }
mkdir -p "$OUT" "$IDX" "$LED"
TS=$(date -u +%Y%m%dT%H%M%SZ)
IDXTS="$IDX/ls3dw_index.tsv"
[ -f "$IDXTS" ] || printf "rel_path\tsha256\tw\th\tbb_sqrt\tinterocular\tpose_bin\tyaw_deg\tlandmarks_tsv\n" > "$IDXTS"
parse_lms(){
  f="$1";
  if grep -qi "^version" "$f" 2>/dev/null && grep -qi "n_points" "$f" 2>/dev/null; then
    awk '/^{/{flag=1;next} /^}/{flag=0} flag{print $1,$2}' "$f" | awk '{printf "%s%s",$0,(NR==68?"\n":" ") }' 
  else
    awk 'NF==2{print $1,$2}' "$f" | awk '{printf "%s%s",$0,(NR==68?"\n":" ") }' 
  fi
}
metrics_from_csv(){
  csv="$1"; yaw="$2";
  # explode into lines
  echo "$csv" | awk '{ for(i=1;i<=NF;i+=2){x[int(i/2)+1]=$i; y[int(i/2)+1]=$(i+1)}
    xmin=x[1]; xmax=x[1]; ymin=y[1]; ymax=y[1];
    for(k=1;k<=68;k++){if(x[k]<xmin)xmin=x[k]; if(x[k]>xmax)xmax=x[k]; if(y[k]<ymin)ymin=y[k]; if(y[k]>ymax)ymax=y[k]; }
    w=xmax-xmin; h=ymax-ymin; bbsqrt=sqrt(w*h);
    # interocular: average of outer eye corners (36 and 45 in 68-pt, 1-indexed), Euclidean distance
    xl=x[37]; yl=y[37]; xr=x[46]; yr=y[46];
    iod=sqrt((xr-xl)^2+(yr-yl)^2);
    print w"\t"h"\t"bbsqrt"\t"iod
  }' 
}
pose_bucket(){ yaw="$1"; case "$yaw" in "" ) echo ""; ;;& esac
  if [ -z "$yaw" ]; then echo ""; return; fi
  y=${yaw#-}; # abs
  if   awk "BEGIN{exit !($y <= 30)}"; then echo "[0,30]";
  elif awk "BEGIN{exit !($y <= 60)}"; then echo "(30,60]";
  else echo "(60,90]"; fi
find "$IN" -type f \( -iname "*.jpg" -o -iname "*.png" -o -iname "*.jpeg" \) | while IFS= read -r img; do
  base="${img%.*}"; cand=""; for ext in pts txt; do [ -f "${base}.${ext}" ] && cand="${base}.${ext}" && break; done
  [ -n "$cand" ] || { echo "skip (no landmarks): $img"; continue; }
  rel="${img#"$IN/"}"; hash=$(sha256sum "$img" | awk "{print \$1}")
  csv=$(parse_lms "$cand" || true)
  [ -n "$csv" ] || { echo "skip (bad landmarks): $img"; continue; }
  # try to read yaw if provided in an optional .yaw or .pose file (single number degrees)
  yaw=""; for ext in yaw pose; do [ -f "${base}.${ext}" ] && yaw=$(awk "NR==1{print \$1}" "${base}.${ext}") && break; done
  met=$(metrics_from_csv "$csv" "$yaw")
  w=$(echo "$met" | awk "{print \$1}")
  h=$(echo "$met" | awk "{print \$2}")
  bbs=$(echo "$met" | awk "{print \$3}")
  iod=$(echo "$met" | awk "{print \$4}")
  bin=$(pose_bucket "$yaw")
  # write one landmarks TSV per image under analysis/morpho/output
  lmtsv="$OUT/${rel%.*}.landmarks.tsv"; mkdir -p "$(dirname "$lmtsv")"
  i=1; echo "$csv" | awk '{ for(j=1;j<=NF;j+=2){k=int(j/2)+1; printf "%d\t%.6f\t%.6f\n", k, $j, $(j+1) } }' > "$lmtsv"
  # append to master index if not present
  if ! grep -Fq "$rel" "$IDXTS"; then
    printf "%s\t%s\t%.6f\t%.6f\t%.6f\t%.6f\t%s\t%s\t%s\n" "$rel" "$hash" "$w" "$h" "$bbs" "$iod" "$bin" "${yaw:-}" "$lmtsv" >> "$IDXTS"
  fi
done
REC="$LED/ls3dw_ingest.receipt.tsv"
[ -f "$REC" ] || printf "TS\t%s\nTOOL\tls3dw_ingest\n" "$TS" > "$REC"
hidx=$(sha256sum "$IDXTS" | awk "{print \$1}")
printf "INDEX_SHA256\t%s\nINDEX_PATH\t%s\n" "$hidx" "$IDXTS" >> "$REC"
