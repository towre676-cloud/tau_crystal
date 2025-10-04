#!/usr/bin/env bash
set -e; set -o pipefail; set +H; umask 022; export LC_ALL=C LANG=C
inp="${1:-.tau_ledger/CHAIN}"
out="${2:-artifacts/entropy/tau_entropy.tsv}"
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
if [ ! -f "$inp" ]; then mkdir -p "$(dirname "$out")" || :; printf "tot\tactive_bins\tH_bits\n0\t0\t0.000000\n" > "$out"; echo "[ok] τ-entropy -> $out (no CHAIN)"; exit 0; fi
mkdir -p "$(dirname "$out")" || :

awk "
  BEGIN { for (i=0;i<16;i++) cnt[i]=0; tot=0; }
  {
    gsub(/\r/,"");
    if (NF==0) next;
    h=$1;
    if (h==\"\") next;
    for (i=1; i<=length(h); i++) {
      c = substr(h,i,1);
      # normalize to lower hex without relying on locale
      if (c==\"A\"||c==\"B\"||c==\"C\"||c==\"D\"||c==\"E\"||c==\"F\") c = sprintf(\"%c\", 97 + (c-\"A\"));
      p = index(\"0123456789abcdef\", c);
      if (p>0) { idx=p-1; cnt[idx]++; tot++; }
    }
  }
  END {
    printf(\"tot\\tactive_bins\\tH_bits\\n\") > \"%s\";
    if (tot==0) { printf(\"0\\t0\\t0.000000\\n\") >> \"%s\"; exit 0; }
    H=0.0; active=0;
    for (i=0;i<16;i++) {
      p = cnt[i]/tot;
      if (p>0) { H += -p*(log(p)/log(2)); active++; }
    }
    printf(\"%d\\t%d\\t%.6f\\n\", tot, active, H) >> \"%s\";
  }
" "$inp" > "$tmp"




mv "$tmp" "$out"
echo "[ok] τ-entropy -> $out"
