#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
sigdir=".tau_ledger/signals"; outdir=".tau_ledger/tau"; mkdir -p "$outdir"
shopt -s nullglob
files=( "$sigdir"/signal-*.tsv )
[ "${#files[@]}" -gt 0 ] || { echo "[err] no signals in $sigdir" >&2; exit 2; }
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
awk -v OFS="\t" 'FNR==1{fi++} {t=$1; v=$2; times[t]=1; key=fi SUBSEP t; val[key]=v} END{ for(tt in times){ printf "%s", tt; for(i=1;i<=fi;i++){ key=i SUBSEP tt; if(key in val) printf OFS "%s", val[key]; else printf OFS "NA"; } printf "\n" } }' "${files[@]}" | sort -n -k1,1 > "$tmp"
awk -f scripts/bin/pav.awk "$tmp" > "$outdir/ensemble.tsv"
echo "$outdir/ensemble.tsv"
