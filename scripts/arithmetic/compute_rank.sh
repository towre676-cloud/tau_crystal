#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
lin=".tau_ledger/langlands/L_tau.json"; out=".tau_ledger/langlands/rank.json"
mkdir -p ".tau_ledger/langlands"
[ -s "$lin" ] || { echo "{\"status\":\"no_L\",\"rank\":null}" > "$out"; echo "$out"; exit 0; }
grid=$(grep -o "\"grid\":[^]]*]" "$lin" | sed -E "s/.*\\[([^]]*)\\].*/\\1/; s/,/ /g")
vals=$(grep -o "\"L\":[^]]*]" "$lin" | sed -E "s/.*\\[([^]]*)\\].*/\\1/; s/,/ /g")
[ -n "$grid" ] || { echo "{\"status\":\"bad\",\"rank\":null}" > "$out"; echo "$out"; exit 0; }
gfile="$(mktemp)"; vfile="$(mktemp)"; for x in $grid; do echo "$x"; done > "$gfile"; for y in $vals; do echo "$y"; done > "$vfile"
getL(){ awk -v t="$1" 'NR==FNR{g[NR]=$1; n=NR; next}{v[FNR]=$1} END{for(i=1;i<=n;i++)if(g[i]==t){print (v[i]>0?v[i]:1e-12); exit}}' "$gfile" "$vfile"; }
L09=$(getL 0.9); L10=$(getL 1.0); L11=$(getL 1.1)
[ -z "$L10" ] && L10=1e-12; [ -z "$L09" ] && L09="$L10"; [ -z "$L11" ] && L11="$L10"
dLleft=$(awk -v a="$L09" -v b="$L10" "BEGIN{print log((b<=0)?1e-12:b)-log((a<=0)?1e-12:a)}")
dLright=$(awk -v a="$L10" -v b="$L11" "BEGIN{print log((b<=0)?1e-12:b)-log((a<=0)?1e-12:a)}")
rank=0; awk -v dl="$dLleft" -v dr="$dLright" "BEGIN{r=(dl<0?1:0)+(dr>0?1:0); if(r<0)r=0; if(r>3)r=3; print r}" > "$vfile"; rank=$(cat "$vfile")
echo "{\"status\":\"ok\",\"rank\":$rank}" > "$out"; rm -f "$gfile" "$vfile"; echo "$out"
