#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022

# Usage: ./morpho_run.sh </path/frontal.jpg> </path/left.jpg> </path/right.jpg>
me="$(basename "$0")"
frontal="${1:-}"; leftp="${2:-}"; rightp="${3:-}"

say(){ printf "%s\n" "$*"; }
die(){ printf "[err] %s\n" "$*" >&2; exit 1; }
abspath(){ (cd "$(dirname "$1")" 2>/dev/null && pwd)/"$(basename "$1")"; }

[ -n "$frontal" ] && [ -n "$leftp" ] && [ -n "$rightp" ] || die "usage: ./$me /abs/frontal.jpg /abs/left.jpg /abs/right.jpg"
[ -f "$frontal" ] || die "missing frontal image: $frontal"
[ -f "$leftp" ]   || die "missing left image: $leftp"
[ -f "$rightp" ]  || die "missing right image: $rightp"

IN_DIR="analysis/morpho/input"
OUT_DIR="analysis/morpho/output"
MANI="analysis/morpho/manifest.tsv"
mkdir -p "$IN_DIR" "$OUT_DIR"

# Normalize absolute paths and copy to a clean input set
FABS="$(abspath "$frontal")"
LABS="$(abspath "$leftp")"
RABS="$(abspath "$rightp")"

ts="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
cp -f "$FABS" "$IN_DIR/frontal.jpg"  || die "copy failed: $FABS"
cp -f "$LABS" "$IN_DIR/left.jpg"     || die "copy failed: $LABS"
cp -f "$RABS" "$IN_DIR/right.jpg"    || die "copy failed: $RABS"

# Stamp a tiny manifest so we always know exactly what was run
printf "timestamp\tfrontal\tleft\tright\n" > "$MANI"
printf "%s\t%s\t%s\t%s\n" "$ts" "$FABS" "$LABS" "$RABS" >> "$MANI"

say "[morpho] staged inputs:"
say "  - $IN_DIR/frontal.jpg  <= $FABS"
say "  - $IN_DIR/left.jpg     <= $LABS"
say "  - $IN_DIR/right.jpg    <= $RABS"
say "[morpho] manifest: $MANI"

# Optional analysis hook: if you add scripts/morpho/analyze.sh, it will run now
if [ -x "scripts/morpho/analyze.sh" ]; then
  say "[morpho] running analysis hook…"
  scripts/morpho/analyze.sh "$IN_DIR/frontal.jpg" "$IN_DIR/left.jpg" "$IN_DIR/right.jpg" "$OUT_DIR" || die "analysis hook failed"
  say "[morpho] outputs in: $OUT_DIR"
else
  say "[morpho] no analyzer present. To add one, create an executable at scripts/morpho/analyze.sh"
  say "           It will receive: frontal left right out_dir"
fi

