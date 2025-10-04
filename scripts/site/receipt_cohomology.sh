#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C

a="${1:-artifacts/site/cover_cocycles.tsv}"
b="${2:-artifacts/hecke/hecke_classes.tsv}"
out="${3:-artifacts/site/cup_product.tsv}"
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
mkdir -p "$(dirname "$out")" || :

if [ ! -f "$a" ] || [ ! -f "$b" ]; then
  echo "[err] need cocycles and hecke classes" >&2; exit 2
fi

awk -v OFS="\t" '
  NR==FNR {                          # build cocycle map
    if (FNR==1) next;                # skip header
    key=$1"-"$2"-"$3; C[key]=$4; next
  }
  FNR==1 { next }                    # skip hecke header
  {
    h=$1; cls=$2;
    if (h=="hash") next;             # extra guard
    if (cls ~ /^[0-9]+$/) {          # numeric class only
      i=((cls+2)%3)+1; j=((cls+1)%3)+1; k=(cls%3)+1;
      key=i"-"j"-"k;
      c=(key in C)?C[key]:0;
      printf "%s\t%d\t%d\n", h, cls, (c*cls)%7919;
    }
  }
' "$a" "$b" > "$tmp"

printf "hash\tclass_modN\tcup_surrogate\n" > "$out"
cat "$tmp" >> "$out"
echo "[ok] cup-product surrogate -> $out"
