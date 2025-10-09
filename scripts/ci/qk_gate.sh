#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
JSON="${1:-./tmp/qk_fit.json}"; RES="${2:-./tmp/qk_residuals.tsv}"; THRESH="${3:-1e-4}"
[ -f "$JSON" ] || { echo "[gate:err] missing $JSON" >&2; exit 2; }
[ -f "$RES" ]  || { echo "[gate:err] missing $RES"  >&2; exit 3; }
N=$(sed -n "s/.*\"n\":\\([0-9][0-9]*\\).*/\\1/p" "$JSON" | head -n1)
A=$(sed -n "s/.*\"linear\":{\"a\":\\([^,]*\\),\"b\":\\([^}]*\\)}.*/\\1/p" "$JSON" | head -n1)
B=$(sed -n "s/.*\"linear\":{\"a\":[^,]*,\"b\":\\([^}]*\\)}.*/\\1/p" "$JSON" | head -n1)
awk -v thr="$THRESH" -v N="$N" -v a="$A" -v b="$B" 'BEGIN{FS="\t"; ok=1; ss=0; m=0}
  /^#/ {next}
  NF>=7 { r=$6; if(r+0!=r){next} ss+=r*r; m++ }
  END{
    rms = (m>0)? sqrt(ss/m) : 1e9;
    if(N<5) ok=0;
    if(rms>thr) ok=0;
    printf("[gate] n=%d m=%d rms=%.8g thr=%g a=%.8g b=%.8g\n", N, m, rms, thr, a, b);
    if(ok) { print "[gate] PASS" } else { print "[gate] FAIL" ; exit 1 }
  }' "$RES"
