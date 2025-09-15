#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
src="analysis/bash_theta_scan.tsv"; out="analysis/endoscopy.tsv"
[ -s "$src" ] || { echo "[skip] $src not found"; exit 0; }
: > "$out"; printf "%s\n" "S_micro\tT_micro\tdiff\tstability" >> "$out"
awk 'NR==1{next} {s=$1;t=$2;d=$3; bucket=int(d/10); H[bucket]++; rows[NR]=$0} END{thr=0; # simple bimodality test
  for(k in H) if(H[k]>thr) thr=H[k]; thr=int(thr/5); for (i in rows){split(rows[i],a,"\t"); d=a[3]; b=int(d/10); stab=(H[b]>=thr?"stable":"unstable"); print a[1] "\t" a[2] "\t" d "\t" stab; }}' "$src" >> "$out"
