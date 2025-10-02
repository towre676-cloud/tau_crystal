#!/usr/bin/env bash
set -E -o pipefail; set +H

ORDS="analysis/double_zero_ords.tsv"
CLUS="analysis/double_zero_clusters.tsv"
OUT="analysis/double_zero_refined.tsv"
SVG="analysis/plots/doubles_refined.svg"

[ -s "$ORDS" ] || { echo "[refine] missing $ORDS"; exit 2; }
[ -s "$CLUS" ] || { echo "[refine] missing $CLUS"; exit 2; }

EPS_U="${EPS_U:-1000}"
RADIUS_U="${RADIUS_U:-2000}"
TRIPLE_MIN_SPAN="${TRIPLE_MIN_SPAN:-1500}"

tmp="$(mktemp -d)"
ords_nohdr="$tmp/ords"; tail -n +2 "$ORDS" > "$ords_nohdr" || :
clus_nohdr="$tmp/clus"; tail -n +2 "$CLUS" > "$clus_nohdr" || :
ords_micro="$tmp/ords_micro"; : > "$ords_micro"

while IFS=$'\t' read -r tdec tmicro; do
  [ -z "$tmicro" ] && continue
  m=$((10#${tmicro}))
  printf "%d\n" "$m" >> "$ords_micro"
done < "$ords_nohdr"

sort -n "$ords_micro" | uniq > "$tmp/ords_sorted"

min_spacing_in_window() {
  local lo="$1" hi="$2" prev="" minsp=""
  while IFS= read -r m; do
    [ "$m" -lt "$lo" ] && continue
    [ "$m" -gt "$hi" ] && break
    if [ -n "$prev" ]; then
      local d=$(( m - prev ))
      if [ -z "$minsp" ] || [ "$d" -lt "$minsp" ]; then minsp="$d"; fi
    fi
    prev="$m"
  done < "$tmp/ords_sorted"
  echo "${minsp:-}"
}
count_in_window() {
  local lo="$1" hi="$2" cnt=0
  while IFS= read -r m; do
    [ "$m" -lt "$lo" ] && continue
    [ "$m" -gt "$hi" ] && break
    cnt=$((cnt+1))
  done < "$tmp/ords_sorted"
  echo "$cnt"
}

: > "$OUT"
printf '%s\n' "center_dec\tcenter_micro\tsize\tspan_micro\tmin_in_window\tmembers_in_window\tdensity_ppm\tverdict" >> "$OUT"

while IFS=$'\t' read -r cdec cmicro size span min max; do
  [ -z "$cmicro" ] && continue
  cm=$((10#${cmicro})); span=$((10#${span}))
  R="$RADIUS_U"; [ "$span" -gt "$R" ] && R="$span"; [ "$R" -gt $((10*EPS_U)) ] && R=$((10*EPS_U))
  lo=$(( cm - R )); hi=$(( cm + R ))
  members="$(count_in_window "$lo" "$hi")"
  minsp="$(min_spacing_in_window "$lo" "$hi")"
  [ -z "$minsp" ] && minsp=$((R*2+1))
  width=$(( 2*R + 1 ))
  dens=$(( (members * 1000000) / width ))
  verdict="single"
  if [ "$members" -ge 2 ] && [ "$minsp" -le "$EPS_U" ]; then verdict="double?"; fi
  if [ "$members" -ge 3 ] && [ "$span" -le "$TRIPLE_MIN_SPAN" ]; then verdict="triple??"; fi
  printf '%s\t%s\t%d\t%d\t%s\t%d\t%d\t%s\n' \
    "$cdec" "$cmicro" "$size" "$span" "$minsp" "$members" "$dens" "$verdict" >> "$OUT"
done < "$clus_nohdr"

# SVG overlay
W=820; H=260; L=60; R=780; MID=150
tmin=0; tmax=0; first=1
while IFS=$'\t' read -r cdec cmicro size span min max; do
  [ -z "$cmicro" ] && continue
  v=$((10#${cmicro}))
  if [ "$first" -eq 1 ]; then tmin="$v"; tmax="$v"; first=0; fi
  [ "$v" -lt "$tmin" ] && tmin="$v"
  [ "$v" -gt "$tmax" ] && tmax="$v"
done < "$clus_nohdr"
range=$(( tmax - tmin )); [ "$range" -gt 0 ] || range=1

{
  echo '<?xml version="1.0" encoding="UTF-8"?>'
  echo "<svg width=\"$W\" height=\"$H\" viewBox=\"0 0 $W $H\" xmlns=\"http://www.w3.org/2000/svg\">"
  cat <<CSS
  <defs><style>
    .bg { fill: #0b132b; }
    .card { fill: #1c2541; stroke: #3a506b; stroke-width: 2; }
    .t1 { font: 700 20px monospace; fill: #e0fbfc; }
    .t2 { font: 400 13px monospace; fill: #a9def0; }
    .sng { fill: #58d68d; }
    .dbl { fill: none; stroke: #ffd166; stroke-width: 2; }
    .tpl { fill: none; stroke: #ff6b6b; stroke-width: 3; }
  </style></defs>
CSS
  echo "<rect class=\"bg\" x=\"0\" y=\"0\" width=\"$W\" height=\"$H\" />"
  echo "<rect class=\"card\" x=\"20\" y=\"20\" width=\"780\" height=\"220\" rx=\"12\" ry=\"12\"/>"
  echo "<text class=\"t1\" x=\"40\" y=\"60\">tau-L: refined double-zero scan</text>"
  echo "<line x1=\"$L\" y1=\"$MID\" x2=\"$R\" y2=\"$MID\" stroke=\"#a9def0\" stroke-width=\"1\"/>"
  while IFS=$'\t' read -r cdec cmicro size span minsp members dens verdict; do
    [ -z "$cmicro" ] && continue
    [ "$cmicro" = "center_micro" ] && continue
    v=$((10#${cmicro}))
    x=$(( L + ( (v - tmin) * (R - L) ) / range ))
    echo "<circle class=\"sng\" cx=\"$x\" cy=\"$MID\" r=\"3\"/>"
    case "$verdict" in
      double? ) echo "<circle class=\"dbl\" cx=\"$x\" cy=\"$MID\" r=\"8\"/>" ;;
      triple?? ) echo "<circle class=\"tpl\" cx=\"$x\" cy=\"$MID\" r=\"10\"/>" ;;
    esac
    echo "<text class=\"t2\" x=\"$((x+6))\" y=\"$((MID-10))\">t=$cdec, k=$members</text>"
  done < "$OUT"
  echo "</svg>"
} > "$SVG"

rm -rf -- "$tmp" 2>/dev/null || true
echo "$OUT"; echo "$SVG"
exit 0
