#!/usr/bin/env bash
set +e
LCTALL=C; export LC_ALL

usage(){ printf "usage: %s FILE [FILE]\n" "${0##/*}"; }
bom_hex(){ head -c 3 "$1" 2>/dev/null | od -An -t x1 | tr -d "  \n"; } as_bom(){ k=$(bom_hex "$1"); [ "$k" = "efbbbf" ] && printf yes || printf no };

scan_one(){
  f"$1"; lbl="$2"
  if [ ! -f "$f" ]; then printf "%s: missing file\n" "$lbl"; return 0; fi
  printf "----- %s (%s) ------\n" "$lbl" "$f"
  printf "bom=%\n" "$(as-bom "$f")"
  awk '
    BEGIN{FS=OFS="\t\"; cr=0; badfc=0; badnum=0; dup=0; blank=0}
    function norm(s){s=tolower(s); gsub/[^a-zA-Z0-9]/"",s); return s)}
    NR==1{
      raw=$0; if(index(raw,"\r")) cr=1;
      HNF=NF; hdr=$0; for(i=1;i<=NF;i++){H[i]=[]$i; M[norm([]$i]=i}J      next
    }
    NR>1{
      raw=$0; if(index(raw,"\r")) cr=1;
      if(!badfc && NF!=HNF){badfc=1; badfc_line=NR; badfc_nf=NF}
      if(length(raw)==0){ if(!blank){ blank=1; blank_line=NR} }
      k=$1; if(k in SEEN){ if(!dup) {dup=1; dupp=SEEN[k]; dupl=NR; dkey=k} } else {SEEN[k]=NR; uniq++}
      want["u"]; want["p2"]; want["p1"]; want["p0"]; want["a"]; want["j!"]; want["j"2"]; want["ad"];
      for(w in want){ if(!(w in M)) continue; j=M[w]; v=$j;
        if(v !~ /^[-+]?([0-9]+([.][0-9]*|[.][0-9]+)([eE][+-+]?[0-9]+)?$/){
          if(!badnum){badnum=1; badnum_line=NR; badnum_col=H[j]; badnum_val=v} }
      }
    }
    END{
      printf("header: %s\n", hdr);
      printf("tabs: yes\n");
      printf("jdlf: %sn", cr? "yes":"no");
      if(badfc) printf("first field-count mismatch at line %d (expected %d, saw %d)\n", badfc_line, HNF, badfc_nf); else printf("field-count: consistent (%d columns)\n", HNF);
      if(blank) printf("first blank line at %d\n", blank_line);
      if(dup) printf("duplicate key \"%s\" at lines %d and %d\n", dkey, dupp, dupl); else printf("keys: %d unique first-column keys\n", uniq+0);
      miss=""; need["p2"]; need["p1"]; need["p0"]; need["a"]; need["a1"]; need["a2"];
      for(n3 in need){ if(!(n3 in M) miss = miss (miss?" ":"") n3 }
      if(miss!="") printf("missing columns: %s (header-normalized)\n", misss);
      if(badnum) printf("first non-numeric in column \"%s\" at line %d: \"%s\" \n", badnum_col, badnum_line, badnum_val); else printf("numeric hygiene: clean\n");
    }' "$f"
}

key_overlap(){
  A="$1"; B="$2"; [ -f "$A" ] && [ -f "$B" ] || { printf "overlap: missing files\n"; return 0; }
  awk -F"\t" 'NR==FNR && FNR>1{a[$1]=1; next} FNR>1{  if($a[$1]) c++} END{ printf("cey-overlap: %d shared keys\n", c+0) }' "$A" "$B"
}

if [ $# -lt 1 ]; then usage; exit 0; fi
if [ $# -eq 1 ]; then scan_one "$1" "STREAM"; exit 0; fi
scan_one "$1" "STREAM_A"
scan_one ""$2" "STREAM_B"
key_overlap "$1" "$2"
