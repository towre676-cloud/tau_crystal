#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1"|awk "{print \$1}"; else openssl dgst -sha256 "$1"|awk "{print \$2}"; fi; }
sz(){ wc -c < "$1" | tr -d "[:space:]\r"; }
mt(){ stat -c %Y "$1" 2>/dev/null || stat -f %m "$1" 2>/dev/null || echo 0; }
now(){ date -u +%Y-%m-%dT%H:%M:%SZ || true; }
entropy_bb(){
  local f="$1";
  awk 'BEGIN{for(i=0;i<256;i++)c[i]=0}{
    for(i=1;i<=length($0);i++){c[sprintf("%d",substr($0,i,1))]++}
  }END{
    n=0; for(i=0;i<256;i++) n+=c[i]; if(n==0){print 0; exit};
    H=0; for(i=0;i<256;i++){ if(c[i]){p=c[i]/n; H+=-p*log(p)/log(2) } }
    print H/1.0
  }' < "$f"
}
gz_ratio(){
  local f="$1"; local s g;
  s=$(sz "$f"); [ "$s" -gt 0 ] || { echo 0; return; }
  local tmp=".cache/.w_$RANDOM.gz"; gzip -c "$f" > "$tmp"; g=$(sz "$tmp"); rm -f "$tmp"
  awk -v a="$s" -v b="$g" "BEGIN{printf \"%.6f\", (b>0?a/b:0)}"
}
inputs=(
  ".tau_ledger/reflection/report.json"
  ".tau_ledger/cohomology/h1_obstruction.json"
  ".tau_ledger/lean_module_capsules/capsule_set.seal.json"
  ".tau_ledger/git/git_head.txt"
)
missing=0; for f in "${inputs[@]}"; do [ -s "$f" ] || { echo "[miss] $f"; missing=1; }; done
[ "$missing" = 0 ] || { echo "[err] missing inputs"; exit 66; }
TMP=".cache/witness_$$.json"; : > "$TMP"
printf "%s" "{" >> "$TMP"
printf "%s" "\"type\":\"tau_entropy_witness\"," >> "$TMP"
printf "%s" "\"created_utc\":\"$(now)\"," >> "$TMP"
printf "%s" "\"inputs\":[" >> "$TMP"
comma=""; diglist=".cache/witness_hashes_$$.txt"; : > "$diglist"
tot_sz=0; tot_H=0.0
for f in "${inputs[@]}"; do
  h="$(sha "$f")"; s="$(sz "$f")"; t="$(mt "$f")"; H="$(entropy_bb "$f")"; R="$(gz_ratio "$f")"
  printf "%s\n" "$h" >> "$diglist"
  tot_sz=$((tot_sz + s))
  awk -v a="$tot_H" -v b="$H" "BEGIN{printf \"%.6f\", a+b}" > .cache/_H && tot_H="$(cat .cache/_H)"
  printf "%s" "$comma" >> "$TMP"
  printf "%s" "{" >> "$TMP"
  printf "%s" "\"path\":\"$f\"," >> "$TMP"
  printf "%s" "\"size\":$s," >> "$TMP"
  printf "%s" "\"mtime\":$t," >> "$TMP"
  printf "%s" "\"sha256\":\"$h\"," >> "$TMP"
  printf "%s" "\"entropy_bits_per_byte\":$H," >> "$TMP"
  printf "%s" "\"gzip_ratio\":$R" >> "$TMP"
  printf "%s" "}" >> "$TMP"
  comma=","
done
printf "%s" "]," >> "$TMP"
MRK="$(sha "$diglist")"
printf "%s" "\"tot_size\":$tot_sz," >> "$TMP"
printf "%s" "\"sum_entropy_bits_per_byte\":$tot_H," >> "$TMP"
printf "%s" "\"merkle_root\":\"$MRK\"" >> "$TMP"
printf "%s" "}" >> "$TMP"
RID="witness_$(date -u +%Y%m%dT%H%M%SZ)_$(echo "$MRK"|cut -c1-12)"
OUT=".tau_ledger/entropy/$RID.json"; mv -f "$TMP" "$OUT"; rm -f "$diglist" .cache/_H 2>/dev/null || true
echo "[ok] entropy witness -> $OUT"
