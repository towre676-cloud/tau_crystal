#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
f="${1:-}"; [ -n "$f" ] && [ -f "$f" ] || { echo "missing csv" >&2; exit 2; }
awk -F, 'BEGIN{bad=0; hdr=0}
{ sub(/\r$/,""); for(i=1;i<=NF;i++){gsub(/^ +| +$/,"",$i)} 
  if(NF==0 || $0 ~ /^[[:space:]]*$/) next
  if(NF<4){bad=1; exit}
  num=0; for(i=1;i<=4;i++){ if($i ~ /^-?[0-9]+(\.[0-9]+)?$/) num++ }
  if(num<4){
    if(hdr==0){hdr=1; next}  # allow exactly one header-like line
    bad=1; exit
  }
}
END{exit bad?1:0}' "$f" || { echo "CSV looks malformed (need rows: Lx,Ly,Rx,Ry, numeric)"; exit 1; }
