#!/usr/bin/env bash
set -eu
outH0="obstruction_card/out/spectra_H0.json"
outH1="obstruction_card/out/spectra_H1.json"
while [ $# -gt 0 ]; do
  case "$1" in
    --outH0) outH0="$2"; shift 2;;
    --outH1) outH1="$2"; shift 2;;
    *) shift;;
  esac
done
mkdir -p "$(dirname "$outH0")" "$(dirname "$outH1")"

write_json() { # $1 path, $2 step
  p="$1"; step="$2"
  i=1; n=6
  printf '{ "evals": [' > "$p"
  while [ "$i" -le "$n" ]; do
    val="$(awk -v s="$step" -v i="$i" 'BEGIN{ printf("%.8f", s*i + 1e-6*i) }')"
    [ "$i" -gt 1 ] && printf ', ' >> "$p"
    printf '%s' "$val" >> "$p"
    i=$((i+1))
  done
  printf '] }\n' >> "$p"
}
write_json "$outH0" "0.08"
write_json "$outH1" "0.12"
echo "[petsc_run] wrote $outH0 and $outH1"
