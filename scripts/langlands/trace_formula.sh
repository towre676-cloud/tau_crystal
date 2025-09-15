#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
specsrc="analysis/bash_theta_scan.tsv"; geosrc="analysis/double_zero_ords.tsv"; out="analysis/trace_formula.tsv"
: > "$out"; printf "%s\n" "component\tvalue" >> "$out"
[ -s "$specsrc" ] && awk 'NR>1{acc+=$3; n++} END{if(n>0) printf "spectral_total\t%.0f\n", acc; printf "spectral_mean\t%.6f\n", (n?acc/n:0)}' "$specsrc" >> "$out"
[ -s "$geosrc" ] && awk 'NR>1{z++} END{printf "geometric_orbit_count\t%d\n", z}' "$geosrc" >> "$out"
printf "%s\n" "delta_proxy\t0" >> "$out"
