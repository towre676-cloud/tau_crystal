#!/usr/bin/env bash
set -Eeu -o pipefail

IN="${1:-}"
OUT="${2:-}"

if [[ -z "${IN}" || -z "${OUT}" ]]; then
  echo "usage: face15_ingest.sh FACE.txt analysis/morpho/face15.tsv" >&2
  exit 2
fi

# Normalize CRLF -> LF on the fly and parse "key: x y" into TSV "x<TAB>y"
awk -F: '
  BEGIN { OFS = "\t" }
  { sub(/\r$/, ""); }                         # strip CR if present
  /^[[:space:]]*#/      { next }              # skip comments
  /^[[:space:]]*$/      { next }              # skip blank
  NF >= 2 {
    key = $1
    rest = $2
    gsub(/^[ \t]+|[ \t]+$/, "", rest)
    n = split(rest, a, /[ \t]+/)
    if (n >= 2 && a[1] != "" && a[2] != "") {
      print a[1], a[2]
      count++
    }
  }
  END {
    if (count == 0) {
      printf("[err] no points parsed from %s\n", ARGV[1]) > "/dev/stderr"
      exit 3
    }
  }
' "$IN" > "$OUT"

# Quick sanity: ensure it looks like numeric pairs
if ! awk 'BEGIN{FS="\t"} NF>=2 && $1+0==$1 && $2+0==$2 {ok++} END{exit(ok>0?0:1)}' "$OUT"; then
  echo "[err] output failed numeric sanity: $OUT" >&2
  exit 4
fi
