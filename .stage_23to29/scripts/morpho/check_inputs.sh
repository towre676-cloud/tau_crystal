#!/usr/bin/env bash
set +H; umask 022
ROOT="analysis/morpho/input"
IM_EXT="png jpg jpeg bmp tif tiff"
LM_EXT="pts json txt csv"
missing=0
[ -d "$ROOT" ] || { echo "[[check]] no $ROOT"; exit 1; }
find "$ROOT" -mindepth 1 -maxdepth 1 -type d -printf "%f\n" | while read -r S; do
  D="$ROOT/$S"; icnt=0; lcnt=0
  for e in $IM_EXT; do c=$(find "$D" -type f -iname "*.$e" | wc -l); icnt=$((icnt+c)); done
  for e in $LM_EXT; do c=$(find "$D" -type f -iname "*.$e" | wc -l); lcnt=$((lcnt+c)); done
  printf "[[check]] %-12s images=%-4s landmarks=%-4s\n" "$S" "$icnt" "$lcnt"
  if [ "$icnt" -eq 0 ] || [ "$lcnt" -eq 0 ]; then missing=$((missing+1)); fi
done
exit $missing
