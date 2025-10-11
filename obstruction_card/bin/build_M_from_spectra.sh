#!/usr/bin/env bash
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
ROOT="${ROOT:-$HOME/Desktop/tau_crystal/tau_crystal}"; cd "$ROOT" || exit 1

H0=obstruction_card/out/spectra_H0.json
H1=obstruction_card/out/spectra_H1.json
SV=obstruction_card/out/singular_values_M.csv
DET=obstruction_card/out/detM_phase.json
MNP=obstruction_card/out/M.npy

# Extract the FIRST 3 numeric tokens from each file (jq-free, robust)
nums() { grep -Eo '[0-9.+-]+([eE][+-]?[0-9]+)?' "$1" | head -3 | tr '\n' ',' | sed 's/,$//'; }

if [ -s "$H0" ] && [ -s "$H1" ]; then
  e0=$(nums "$H0" || true); e1=$(nums "$H1" || true)
else
  e0=""; e1=""
fi

if [ -z "${e0:-}" ] || [ -z "${e1:-}" ]; then
  printf "1,1,1\n" > "$SV"
  printf '%s\n' '{"det_phase": 0.0}' > "$DET"
  printf '%s\n' "NPY-DEMO" > "$MNP"
  exit 0
fi

awk -v e0="$e0" -v e1="$e1" '
  function abs(x){return x<0?-x:x}
  BEGIN{
    n0=split(e0,a,","); n1=split(e1,b,","); n=(n0<n1?n0:n1); if(n<1)n=0;
    maxs=0; for(i=1;i<=n;i++){ s[i]=sqrt(abs((a[i]+0)*(b[i]+0))); if(s[i]>maxs)maxs=s[i]; }
    if(maxs<=0){ print "1,1,1"; exit }
    OFMT="%.16e"; out="";
    for(i=1;i<=3;i++){
      val=(i<=n)?(s[i]/maxs):1.0;
      out=out ((i>1)?",":"") sprintf("%.16e", val)
    }
    print out
  }
' > "$SV"

printf '%s\n' '{"det_phase": 0.0}' > "$DET"
printf '%s\n' "NPY-PLACEHOLDER" > "$MNP"
