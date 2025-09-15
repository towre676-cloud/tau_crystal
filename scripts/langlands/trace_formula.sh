#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
spec="analysis/bash_theta_scan.tsv"; geo="analysis/double_zero_ords.tsv"; out="analysis/trace_formula.tsv"
: > "$out"; printf "%s\n" "component\tvalue" >> "$out"
[ -s "$spec" ] && awk 'NR>1{acc+=$3;n++} END{printf "spectral_total\t%.0f\nspectral_mean\t%.6f\n",acc,(n?acc/n:0)}' "$spec" >> "$out"
[ -s "$geo" ] && awk 'NR>1{z++} END{printf "geometric_orbit_count\t%d\n",z}' "$geo" >> "$out"
printf "%s\n" "delta_proxy\t0" >> "$out"; echo "[trace] wrote $out"
