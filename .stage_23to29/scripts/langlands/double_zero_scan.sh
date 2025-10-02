#!/usr/bin/env bash
# Git Bash safe: no -u, no process substitution, ASCII only.
set -E -o pipefail; set +H
. scripts/langlands/_bash_math.sh 2>/dev/null || true

OUT_DIR="analysis"; PLOT_DIR="analysis/plots"
mkdir -p "$OUT_DIR" "$PLOT_DIR"

# tolerances (decimals) -> micro ints; fallback if helper missing
EPS_DEC="${EPS_DEC:-0.001}"
T_MAX_DEC="${T_MAX_DEC:-10000}"
dec_to_micro_fallback() { v="$1"; s=""; case "$v" in -*) s="-"; v="${v#-}";; esac
  case "$v" in .*) v="0$v";; esac
  a="${v%%.*}"; b="${v#*.}"; [ "$a" = "$v" ] && b=""
  while [ "${#b}" -lt 6 ]; do b="${b}0"; done
  printf '%s%d\n' "$s" $(( 10#${a:-0}*1000000 + 10#${b:-0} ))
}
to_micro() {
  if command -v dec_to_micro >/dev/null 2>&1; then
    dec_to_micro "$1" 2>/dev/null || dec_to_micro_fallback "$1"
  else
    dec_to_micro_fallback "$1"
  fi
}
EPS_U="$(to_micro "$EPS_DEC")"; [ -n "$EPS_U" ] || EPS_U=1000
T_MAX_U="$(to_micro "$T_MAX_DEC")"; [ -n "$T_MAX_U" ] || T_MAX_U=10000000000

# keys to scan under arrays; override via: KEYS="t zeros ordinates ..."
KEYS="${KEYS:-zeros critical t_crit tcrit turing_zeros imag_zeros rho ordinates critical_line_zeros ordinates_t zeros_t tau_zeros gl2_zeros t}"

# default scan roots
if [ "$#" -eq 0 ]; then set -- .tau_ledger analysis; fi

tmp="$(mktemp -d)"
raw="$tmp/all_dec.txt"; : > "$raw"
files="$tmp/files0"; : > "$files"

# build list of json files
for d in "$@"; do
  [ -d "$d" ] || continue
  find "$d" -type f -name '*.json' -print0 2>/dev/null >> "$files"
done

emit_t() {
  f="$1"; base="${f##*/}"
  flat="$tmp/flat.$$"

  # special-case: automorphic/new_zeros.json is a plain numeric array of ordinates
  if [ "$base" = "new_zeros.json" ]; then
    tr -d '\r\n' < "$f" > "$flat" 2>/dev/null || return 0
    tr ',{}' '   ' < "$flat" | tr '[]' '  ' | tr ' ' '\n' \
      | grep -E '^-?[0-9]+(\.[0-9]+)?$' >> "$raw" || true
    rm -f "$flat"
    return 0
  fi

  tr -d '\r\n' < "$f" > "$flat" 2>/dev/null || return 0

  # arrays under known keys (env-configurable)
  for key in $KEYS; do
    grep -Eo "\"$key\"[[:space:]]*:[[:space:]]*\[[^]]*\]" "$flat" 2>/dev/null \
    | sed -E 's/^[^[]*\[//; s/\].*$//' \
    | tr ',{}' '   ' \
    | tr ':' '\n' \
    | tr '[]' '  ' \
    | tr ' ' '\n' \
    | grep -E '^-?[0-9]+(\.[0-9]+)?$' >> "$raw" || true
  done

  # object fields with t-like names
  grep -Eo '"(t|im|Im|imag|im_part|zero_t)"[[:space:]]*:[[:space:]]*-?[0-9]+(\.[0-9]+)?' "$flat" 2>/dev/null \
    | sed -E 's/.*:\s*//' >> "$raw" || true

  rm -f "$flat"
}

# walk files list
while IFS= read -r -d '' j; do emit_t "$j"; done < "$files"

# convert to micro + clip by T_MAX
micro="$tmp/all_micro.txt"; : > "$micro"
while IFS= read -r x; do
  [ -z "$x" ] && continue
  m="$(to_micro "$x" 2>/dev/null || echo 0)"; m=$((10#${m}))
  absm="$m"; [ "$absm" -lt 0 ] && absm=$(( -absm ))
  [ "$absm" -le "$T_MAX_U" ] || continue
  printf '%d\n' "$m" >> "$micro"
done < "$raw"

ords_tsv="$OUT_DIR/double_zero_ords.tsv"
clu_tsv="$OUT_DIR/double_zero_clusters.tsv"
: > "$ords_tsv"; printf '%s\n' "t_dec\tt_micro" >> "$ords_tsv"
: > "$clu_tsv"; printf '%s\n' "center_dec\tcenter_micro\tsize\tspan_micro\tmin_micro\tmax_micro" >> "$clu_tsv"

if [ -s "$micro" ]; then
  sort -n "$micro" | uniq > "$tmp/sorted.txt"

  # all ordinates
  while IFS= read -r m; do
    s=""; mm="$m"; if [ "$mm" -lt 0 ]; then s="-"; mm=$(( -mm )); fi
    printf '%s%d.%06d\t%s%s\n' "$s" $(( mm/1000000 )) $(( mm%1000000 )) "$s" "$mm" >> "$ords_tsv"
  done < "$tmp/sorted.txt"

  # cluster by EPS_U
  prev_set=0
  cluster_min=0; cluster_max=0; cluster_size=0
  flush_cluster() {
    if [ "$cluster_size" -ge 2 ]; then
      c=$(( (cluster_min + cluster_max) / 2 ))
      sign=""; ca="$c"; if [ "$ca" -lt 0 ]; then sign="-"; ca=$(( -ca )); fi
      printf '%s%d.%06d\t%s%s\t%d\t%d\t%s\t%s\n' \
        "$sign" $(( ca/1000000 )) $(( ca%1000000 )) \
        "$sign" "$c" \
        "$cluster_size" $(( cluster_max - cluster_min )) \
        "$cluster_min" "$cluster_max" >> "$clu_tsv"
    fi
  }
  while IFS= read -r v; do
    v=$((10#${v}))
    if [ "$prev_set" -eq 0 ]; then
      cluster_min="$v"; cluster_max="$v"; cluster_size=1; prev="$v"; prev_set=1; continue
    fi
    diff=$(( v - prev ))
    if [ "$diff" -le "$EPS_U" ]; then
      cluster_max="$v"; cluster_size=$(( cluster_size + 1 ))
    else
      flush_cluster
      cluster_min="$v"; cluster_max="$v"; cluster_size=1
    fi
    prev="$v"
  done < "$tmp/sorted.txt"
  flush_cluster
else
  echo "[dz] no ordinates found (adjust EPS_DEC/KEYS or keys)" >&2
fi

# tiny SVG (always)
svg="$PLOT_DIR/doubles.svg"
W=720; H=240; L=40; R=680; MID=140
tmin=0; tmax=0; first=1
tmpclu="$tmp/clu_nohdr.txt"; : > "$tmpclu"
if [ -s "$clu_tsv" ]; then tail -n +2 "$clu_tsv" > "$tmpclu" || true; fi
if [ -s "$tmpclu" ]; then
  while IFS=$'\t' read -r cdec cmicro size span min max; do
    [ -z "$cmicro" ] && continue
    v=$((10#${cmicro}))
    if [ "$first" -eq 1 ]; then tmin="$v"; tmax="$v"; first=0; fi
    [ "$v" -lt "$tmin" ] && tmin="$v"
    [ "$v" -gt "$tmax" ] && tmax="$v"
  done < "$tmpclu"
fi
range=$(( tmax - tmin )); [ "$range" -gt 0 ] || range=1

{
  echo '<?xml version="1.0" encoding="UTF-8"?>'
  echo "<svg width=\"$W\" height=\"$H\" viewBox=\"0 0 $W $H\" xmlns=\"http://www.w3.org/2000/svg\">"
  cat <<CSS
  <defs><style>
    .bg { fill: #0b132b; }
    .card { fill: #1c2541; stroke: #3a506b; stroke-width: 2; }
    .t1 { font: 700 20px monospace; fill: #e0fbfc; }
    .t2 { font: 400 14px monospace; fill: #a9def0; }
    .dot { fill: #58d68d; }
    .none { fill: #ff6b6b; }
  </style></defs>
CSS
  echo "<rect class=\"bg\" x=\"0\" y=\"0\" width=\"$W\" height=\"$H\" />"
  echo "<rect class=\"card\" x=\"20\" y=\"20\" width=\"680\" height=\"200\" rx=\"12\" ry=\"12\"/>"
  echo "<text class=\"t1\" x=\"40\" y=\"60\">tau-L: double-zero candidates (eps=${EPS_DEC})</text>"
  if [ -s "$tmpclu" ]; then
    echo "<line x1=\"$L\" y1=\"$MID\" x2=\"$R\" y2=\"$MID\" stroke=\"#a9def0\" stroke-width=\"1\"/>"
    while IFS=$'\t' read -r cdec cmicro size span min max; do
      [ -z "$cmicro" ] && continue
      v=$((10#${cmicro}))
      x=$(( L + ( (v - tmin) * (R - L) ) / range ))
      r=$(( 3 + (size>2 ? size : 0) ))
      echo "<circle class=\"dot\" cx=\"$x\" cy=\"$MID\" r=\"$r\"/>"
      echo "<text class=\"t2\" x=\"$((x+6))\" y=\"$((MID-10))\">t=$cdec (x$size)</text>"
    done < "$tmpclu"
  else
    echo "<text class=\"t2 none\" x=\"40\" y=\"110\">no clusters (size >= 2) within eps</text>"
  fi
  echo "</svg>"
} > "$svg"

# explicit cleanup for Git Bash
rm -rf -- "$tmp" 2>/dev/null || true
echo "$ords_tsv"; echo "$clu_tsv"; echo "$svg"
exit 0
