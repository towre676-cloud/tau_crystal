#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
[ "${ENTROPY_DEBUG:-0}" = "1" ] && set -x || true
A="${1:-}"; B="${2:-}"
[ -n "$A" ] && [ -n "$B" ] || { echo "[err] usage: witness_compare.sh OLD.json NEW.json"; exit 64; }
[ -f "$A" ] || { echo "[err] not found: $A"; exit 66; }
[ -f "$B" ] || { echo "[err] not found: $B"; exit 66; }
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1"|awk "{print \$1}"; else openssl dgst -sha256 "$1"|awk "{print \$2}"; fi; }
now(){ date -u +%Y-%m-%dT%H:%M:%SZ || true; }
A_TSV=".cache/wc_A_$$.tsv"; B_TSV=".cache/wc_B_$$.tsv"; : > "$A_TSV"; : > "$B_TSV"
stream_extract(){
  awk '
  BEGIN{ins=0}
  {line=$0; gsub("\r","",line);
   if(!ins){ if(line~/"inputs":[[]/){ ins=1; sub(/^.*"inputs":\[/,"",line) } else next }
   buf=buf line; if(index(line,"]")>0){ ins=2 }
  }
  END{
    if(buf=="") exit;
    sub(/^\[/,"",buf); sub(/\]$/,"",buf); gsub(/\}\s*,\s*\{/,"\n",buf);
    n=split(buf,rows,"\n");
    for(i=1;i<=n;i++){
      r=rows[i]; gsub(/^\{/,"",r); gsub(/\}$/,"",r);
      p=""; sz="0"; ent="0"; gr="0";
      if(match(r,/"path":"[^"]+"/)){ m=substr(r,RSTART,RLENGTH); sub(/"path":"/,"",m); sub(/"$/,"",m); p=m }
      if(match(r,/"size":[0-9]+/)){ m=substr(r,RSTART,RLENGTH); sub(/"size":/,"",m); sz=m }
      if(match(r,/"entropy_bits_per_byte":[0-9.]+/)){ m=substr(r,RSTART,RLENGTH); sub(/"entropy_bits_per_byte":/,"",m); ent=m }
      if(match(r,/"gzip_ratio":[0-9.]+/)){ m=substr(r,RSTART,RLENGTH); sub(/"gzip_ratio":/,"",m); gr=m }
      if(p!=""){ printf "%s\t%s\t%s\t%s\n", p, sz, ent, gr }
    }
  }'
}
stream_extract < "$A" > "$A_TSV"
stream_extract < "$B" > "$B_TSV"
AWKOUT=".cache/wc_rows_$$.jsonl"; : > "$AWKOUT"
: > "$AWKOUT"
awk -v out="$AWKOUT" -F "\t" '
NR==FNR{a[$1]=$0; next}
{b[$1]=$0} END{
  for(k in a) keys[k]=1; for(k in b) keys[k]=1;
  q=34; nl=10;
  for(k in keys){
    split(a[k],A,"\t"); split(b[k],B,"\t"); p=k;
    as=(A[2]==""?0:A[2])+0; bs=(B[2]==""?0:B[2])+0;
    ae=(A[3]==""?0:A[3])+0; be=(B[3]==""?0:B[3])+0;
    ar=(A[4]==""?0:A[4])+0; br=(B[4]==""?0:B[4])+0;
    ds=bs-as; de=be-ae; dr=br-ar;
    printf("{%cpath%c:%c%s%c,%csize%c:{%cold%c:%d,%cnew%c:%d,%cdelta%c:%d},", q,q,q,p,q,q,q,q,q,as,q,q,bs,q,q,ds) > out
    printf("%centropy_bits_per_byte%c:{%cold%c:%.6f,%cnew%c:%.6f,%cdelta%c:%.6f},", q,q,q,q,ae,q,q,be,q,q,de) > out
    printf("%cgzip_ratio%c:{%cold%c:%.6f,%cnew%c:%.6f,%cdelta%c:%.6f}}%c", q,q,q,q,ar,q,q,br,q,q,dr,nl) > out
  }
}' "$A_TSV" "$B_TSV"
OUTTMP=".cache/wc_out_$$.json"; : > "$OUTTMP"
printf "%s" "{" >> "$OUTTMP"
printf "%s" "\"type\":\"tau_entropy_compare\"," >> "$OUTTMP"
printf "%s" "\"created_utc\":\"$(now)\"," >> "$OUTTMP"
printf "%s" "\"old_receipt\":\"$A\"," >> "$OUTTMP"
printf "%s" "\"new_receipt\":\"$B\"," >> "$OUTTMP"
printf "%s" "\"old_sha\":\"$(sha "$A")\"," >> "$OUTTMP"
printf "%s" "\"new_sha\":\"$(sha "$B")\"," >> "$OUTTMP"
printf "%s" "\"entries\":[" >> "$OUTTMP"
comma=""; while IFS= read -r line; do printf "%s" "$comma" >> "$OUTTMP"; printf "%s" "$line" >> "$OUTTMP"; comma=","; done < "$AWKOUT"
printf "%s" "]," >> "$OUTTMP"
tot_as=0; while IFS=$'\t' read -r p s e r; do tot_as=$((tot_as + s)); done < "$A_TSV"
tot_bs=0; while IFS=$'\t' read -r p s e r; do tot_bs=$((tot_bs + s)); done < "$B_TSV"
printf "%s" "\"summary\":{" >> "$OUTTMP"
printf "%s" "\"total_size_old\":$tot_as," >> "$OUTTMP"
printf "%s" "\"total_size_new\":$tot_bs," >> "$OUTTMP"
printf "%s" "\"total_size_delta\":$((tot_bs - tot_as))" >> "$OUTTMP"
printf "%s" "}" >> "$OUTTMP"
printf "%s" "}" >> "$OUTTMP"
RID="entropy_compare_$(date -u +%Y%m%dT%H%M%SZ)_$(echo "$(sha "$OUTTMP")"|cut -c1-12)"
OUT=".tau_ledger/entropy/$RID.json"; mv -f "$OUTTMP" "$OUT"
rm -f "$A_TSV" "$B_TSV" "$AWKOUT" 2>/dev/null || true
echo "[ok] compare -> $OUT"
