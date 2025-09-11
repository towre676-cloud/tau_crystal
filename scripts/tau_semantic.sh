#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
# Usage: tau_semantic.sh <textA-file> <textB-file>
# Outputs JSON with cosine_bow, jaccard_2gram, and optional cosine_embed.
A="${1:-}"; B="${2:-}"; [ -f "$A" ] && [ -f "$B" ] || { echo "{\"ok\":false,\"error\":\"usage: tau_semantic.sh <A> <B>\"}"; exit 2; }
norm(){ tr -d "\r" | tr "[:upper:]" "[:lower:]" | tr -cs "[:alnum:]" "\n" ; }
bow(){ norm | awk 'length($0)>1{c[$0]++} END{for(k in c) printf "%s %d\n",k,c[k]}' | sort ; }
cosine_bow(){
  fA=$(mktemp); fB=$(mktemp); trap 'rm -f "$fA" "$fB"' EXIT
  bow < "$A" > "$fA"; bow < "$B" > "$fB"
  awk 'NR==FNR{a[$1]=$2; next}{b[$1]=$2} END{for(k in a){dot+=a[k]*b[k]} for(k in a){na+=a[k]*a[k]} for(k in b){nb+=b[k]*b[k]} if(na==0||nb==0){print 0; exit} printf "%.6f\n", dot/(sqrt(na)*sqrt(nb))}' "$fA" "$fB"
}
jaccard2(){
  sA=$(mktemp); sB=$(mktemp); trap 'rm -f "$sA" "$sB"' RETURN
  # build 2-gram shingles (word bigrams)
  for F in "$A" "$B"; do
    tr -d "\r" < "$F" | tr "[:upper:]" "[:lower:]" | tr -cs "[:alnum:]" " " | awk '{for(i=1;i<NF;i++) printf "%s_%s\n",$i,$(i+1)}' | sort -u > "${F}.sh2"
  done
  comm -12 "$A.sh2" "$B.sh2" | wc -l > "$sA"
  cat "$A.sh2" "$B.sh2" | sort -u | wc -l > "$sB"
  inter=$(cat "$sA"); uni=$(cat "$sB"); [ "$uni" -eq 0 ] && { echo 0; return; }
  awk -v i="$inter" -v u="$uni" 'BEGIN{printf "%.6f\n", (i+0.0)/u}' 
  rm -f "$A.sh2" "$B.sh2"
}
cosine_embed(){
  [ -n "${TAU_EMBED_CMD:-}" ] || { echo ""; return; }
  fa=$(mktemp); fb=$(mktemp); trap 'rm -f "$fa" "$fb"' RETURN
  # Expect TAU_EMBED_CMD to read stdin and output floats (space/comma separated)
  tr -d "\r" < "$A" | eval "$TAU_EMBED_CMD" | tr "," " " | tr -s " " > "$fa" || true
  tr -d "\r" < "$B" | eval "$TAU_EMBED_CMD" | tr "," " " | tr -s " " > "$fb" || true
  awk 'NR==FNR{for(i=1;i<=NF;i++) a[i]+=$i; next}{for(i=1;i<=NF;i++) b[i]+=$i} END{for(i=1;i<=length(a);i++){dot+=a[i]*b[i]; na+=a[i]*a[i]; nb+=b[i]*b[i]} if(na==0||nb==0){print ""; exit} printf "%.6f\n", dot/(sqrt(na)*sqrt(nb))}' "$fa" "$fb"
}
cb=$(cosine_bow)
jc=$(jaccard2)
ce=$(cosine_embed || true)
if [ -n "$ce" ]; then printf "{\"ok\":true,\"cosine_bow\":%s,\"jaccard_2gram\":%s,\"cosine_embed\":%s}\n" "$cb" "$jc" "$ce"; else printf "{\"ok\":true,\"cosine_bow\":%s,\"jaccard_2gram\":%s}\n" "$cb" "$jc"; fi
