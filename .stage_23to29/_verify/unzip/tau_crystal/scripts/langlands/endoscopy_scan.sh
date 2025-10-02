#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
src="analysis/bash_theta_scan.tsv"; out="analysis/endoscopy.tsv"
[ -s "$src" ] || { echo "[endoscopy] skip: $src missing"; exit 0; }
: > "$out"; printf "%s\n" "S_micro\tT_micro\tdiff\tstability" >> "$out"
awk 'NR==1{next} {s=$1;t=$2;d=$3; b=int(d/10); H[b]++; R[NR]=$0} END{thr=0; for(k in H) if(H[k]>thr) thr=H[k]; thr=int(thr/5); for(i in R){split(R[i],a,"\t"); b=int(a[3]/10); stab=(H[b]>=thr?"stable":"unstable"); print a[1] "\t" a[2] "\t" a[3] "\t" stab}}' "$src" >> "$out"; echo "[endoscopy] wrote $out"
