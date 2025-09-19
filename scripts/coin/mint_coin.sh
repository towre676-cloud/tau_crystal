#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022

label="${1:-11a1}"
pmax="${2:-199}"
ap="analysis/atlas/${label}/ap.tsv"
atlas="analysis/atlas.jsonl"
hecke="analysis/atlas/atlas_hecke.jsonl"

sha256_file(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'; return; fi
               if command -v shasum    >/dev/null 2>&1; then shasum -a 256 "$1" | awk '{print $1}'; return; fi
               openssl dgst -sha256 "$1" 2>/dev/null | awk '{print $NF}'; }

[ -s "$ap" ] || { echo "[coin] missing $ap" >&2; exit 4; }
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || echo "1970-01-01T00:00:00Z")
g=$(git rev-parse --short=12 HEAD 2>/dev/null || echo nogit)

tmpd=$(mktemp -d 2>/dev/null || mktemp -d -t coin)
panel="$tmpd/ap_panel.tsv"; : > "$panel"
tr -d '\r' < "$ap" | awk -v P="$pmax" '$1 ~ /^[0-9]+$/ && $2 ~ /^-?[0-9]+$/ && $1+0<=P {printf "%d\t%d\n",$1,$2}' | sort -n -k1,1 > "$panel"
[ -s "$panel" ] || { echo "[coin] empty panel after normalize" >&2; rm -rf "$tmpd"; exit 5; }

cond=$(awk -v L="$label" 'index($0,"\"label\":\"" L "\""){ if (match($0,/"conductor":[ ]*[0-9]+/)) { s=substr($0,RSTART,RLENGTH); gsub(/[^0-9]/,"",s); print s; exit } }' "$hecke" 2>/dev/null)
[ -n "$cond" ] || cond=0

panel_sha=$(sha256_file "$panel")

tau=$(awk 'BEGIN{MOD=1000000007; have0=0; u0=1; u1=0; s=0}
{ if(NF<2) next; ap=$2; apm=((ap%MOD)+MOD)%MOD;
  if(have0==0){u1=apm; s=(u0+u1)%MOD; have0=1; next;}
  u2=( (apm*u1)%MOD - u0 )%MOD; if(u2<0) u2+=MOD;
  s=(s+u2)%MOD; u0=u1; u1=u2 }
END{print s%MOD}' "$panel")

mirror_ok=false; adv_ok=false
if [ -s "$atlas" ]; then
  m=$(awk -v L="$label" 'BEGIN{last=""} /"type":"MIRROR_ATLAS"/ { if (index($0,"\"label\":\"" L "\"")) last=$0 } END{print last}' "$atlas")
  a=$(awk -v L="$label" 'BEGIN{last=""} /"type":"ADVERSARIAL_RECOUNT"/ { if (index($0,"\"label\":\"" L "\"")) last=$0 } END{print last}' "$atlas")
  printf "%s" "$m" | grep -q '"mirror_ok":true' && mirror_ok=true
  printf "%s" "$a" | grep -q '"agree":true'      && adv_ok=true
fi

C="$tmpd/coin.json"; : > "$C"
printf "%s" "{"                               >> "$C"
printf "%s" "\"schema\":\"taucrystal/coin/v1\"," >> "$C"
printf "%s" "\"label\":\"$label\","           >> "$C"
printf "%s" "\"conductor\":$cond,"            >> "$C"
printf "%s" "\"pmax\":$pmax,"                 >> "$C"
printf "%s" "\"panel_sha256\":\"$panel_sha\"," >> "$C"
printf "%s" "\"tau_int\":$tau,"               >> "$C"
printf "%s" "\"mirror_ok\":$mirror_ok,"       >> "$C"
printf "%s" "\"adversarial_ok\":$adv_ok,"     >> "$C"
printf "%s" "\"commit\":\"$g\","              >> "$C"
printf "%s" "\"ts\":\"$ts\""                  >> "$C"
printf "%s\n" "}"                             >> "$C"

coin_sha=$(sha256_file "$C"); short=${coin_sha:0:12}
pack="witness-${label}-${ts//[:]/-}-${short}.tar.gz"
( cd "$tmpd" && tar -czf "../$pack" --owner=0 --group=0 --format=ustar coin.json ap_panel.tsv ) || { echo "[coin] tar failed"; rm -rf "$tmpd"; exit 9; }
mv "$pack" . 2>/dev/null || true
echo "[coin] minted $pack  (coin_sha=$coin_sha panel_sha=$panel_sha tau=$tau)"
rm -rf "$tmpd"
