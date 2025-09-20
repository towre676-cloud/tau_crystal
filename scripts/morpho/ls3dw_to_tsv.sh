#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
SRC="${1:-}"
[ -n "$SRC" ] && [ -d "$SRC" ] || { echo "usage: $0 /path/to/LS3D-W"; exit 2; }
OUT="analysis/morpho/ref/datasets/ls3d_landmarks.tsv"
mkdir -p "$(dirname "$OUT")"; : > "$OUT"
shopt -s nullglob
count=0
while IFS= read -r -d "" f; do
  id="$(basename "$f" .pts)"
  np=$(awk 'tolower($1$2) ~ /^n_points:/ {print $2; exit}' "$f")
  [ -z "$np" ] && np=68
  mapfile -t coords < <(awk '/\{/{inb=1; next} /\}/{inb=0} inb && NF>=2 {printf "%.8f %.8f\n", $1, $2}' "$f")
  [ "${#coords[@]}" -lt "$np" ] && { echo "warn: $f has ${#coords[@]}/$np points; skipping"; continue; }
  row="$id"; i=0
  while [ "$i" -lt "$np" ]; do
    xy=(${coords[$i]}); row="$row\t${xy[0]}\t${xy[1]}\t0.00000000"; i=$((i+1))
  done
  printf "%b\n" "$row" >> "$OUT"; count=$((count+1))
done < <(find "$SRC" -type f -name "*.pts" -print0)
echo "LS3D-W: wrote $count rows to $OUT"
