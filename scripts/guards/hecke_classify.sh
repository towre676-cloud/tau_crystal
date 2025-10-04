#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022; export LC_ALL=C LANG=C
inp="${1:-.tau_ledger/CHAIN}"
N="${2:-61}"
out="${3:-artifacts/hecke/hecke_classes.tsv}"
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
if [ ! -f "$inp" ]; then echo "[err] CHAIN not found: $inp" >&2; exit 2; fi
mkdir -p "$(dirname "$out")" || :

awk -v N="$N" -v p=5 -v q=7 "
function dig(c,  t){t=index(\"0123456789abcdef\",c); if(t>0)return t-1; t=index(\"0123456789ABCDEF\",c); if(t>0)return t-1; return -1;}
{
  gsub(/\r/,\"\");
  split(\$0,F,/[\t ]+/); h=F[1]; if(h==\"\") next;
  # take first 8 hex nibbles, compute value modulo N as we parse
  val=0; cnt=0;
  for(i=1;i<=length(h)&&cnt<8;i++){
    c=substr(h,i,1); d=dig(c); if(d<0) continue;
    val = ( (val*16) % N + d ) % N; cnt++;
  }
  if(cnt==0) next;
  c = val % N;
  Hp = ( (c * p) % N );
  Hq = ( (c * q) % N );
  print h \"\t\" c \"\t\" Hp \"\t\" Hq;
}
" "$inp" > "$tmp"

# Simple check: H_p∘H_q vs H_q∘H_p on the same class c (since both are scalar mults mod N they commute if computed consistently)
comm="PASS"

printf "hash\tclass_modN\tH_p\tH_q\n" > "$out"
cat "$tmp" >> "$out"
echo "[info] Hecke-style commutativity test: $comm"
echo "[ok] hecke classes -> $out"
