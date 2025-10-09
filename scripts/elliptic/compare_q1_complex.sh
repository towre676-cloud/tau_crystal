#!/usr/bin/env bash
set -euo pipefail

A="${1:-}"
B="${2:-}"
OUT="${3:-tsv/elliptic_q1_central_sigma.tsv}"
REC="tsv/elliptic_pass2_receipt.json"

[ -n "$A" ] && [ -n "$B" ] || { echo "[err] usage: $0 A.tsv B.tsv [OUT]"; exit 2; }
[ -f "$A" ] && [ -f "$B" ] || { echo "[err] missing input TSV(s)"; exit 2; }

# AWK parses either a+bj / a-bj or paired Re_/Im_ columns.
awk -F'\t' -v A="$A" -v B="$B" '
function trim(s){ gsub(/^[ \t]+|[ \t]+$/,"",s); return s }
function parse_c(s,   m,re,im){
  s=trim(s);
  if (s ~ /[jJ]$/) {
    # match like +a±bj (allow missing + on real)
    if (match(s, /^([+-]?[0-9.]+([eE][+-]?[0-9]+)?)?([+-][0-9.]+([eE][+-]?[0-9]+)?)?[jJ]$/, m)) {
      re = (m[1] ? m[1] : 0)+0; im = (m[3] ? m[3] : 0)+0; return re "," im
    }
  }
  # fallback: treat as real
  if (s == "" || s == "NA") return "0,0"
  return (s+0) ",0"
}
NR==FNR {
  # read header of A
  if (FNR==1) {
    for (i=1;i<=NF;i++) { hA[i]=$i; idxA[$i]=i }
    next
  }
  if ($0 ~ /^#/ || NF<1) next
  key=$1
  # stash entire row
  for (i=1;i<=NF;i++) rowA[key,i]=$i
  keys[key]=1
  next
}
FNR==1 {
  # read header of B
  for (i=1;i<=NF;i++) { hB[i]=$i; idxB[$i]=i }
  # Build list of complex series names:
  # 1) unified "name" if we have both Re_name and Im_name
  # 2) any column in either file that looks like complex a+bj at data time will be parsed later.
  split("", hasRe); split("", hasIm)
  for (c in idxA) if (c ~ /^Re_/) hasRe[substr(c,4)]=1
  for (c in idxA) if (c ~ /^Im_/) hasIm[substr(c,4)]=1
  for (c in idxB) if (c ~ /^Re_/) hasRe[substr(c,4)]=1
  for (c in idxB) if (c ~ /^Im_/) hasIm[substr(c,4)]=1
  nS=0
  for (nm in hasRe) if (hasIm[nm]) { series[++nS]=nm; seenSeries[nm]=1 }

  # also add any single columns from A that might carry complex literal later
  for (i=2;i in hA;i++){
    nm=hA[i]; if (!(nm in seenSeries) && nm !~ /^(Re_|Im_)/) { singleA[nm]=1 }
  }
  for (i=2;i in hB;i++){
    nm=hB[i]; if (!(nm in seenSeries) && nm !~ /^(Re_|Im_)/) { singleB[nm]=1 }
  }
  # union singles
  for (nm in singleA) if (!seenSeries[nm]) series[++nS]=nm
  for (nm in singleB) if (!seenSeries[nm]) {
    found=0; for (j=1;j<=nS;j++) if (series[j]==nm) {found=1;break}
    if(!found) series[++nS]=nm
  }

  # header
  printf "key"
  for (i=1;i<=nS;i++){
    nm=series[i]
    printf "\tcentral_re[%s]\tcentral_im[%s]\tsigma_re[%s]\tsigma_im[%s]\tabs_central[%s]\tsigma_abs[%s]", nm,nm,nm,nm,nm,nm
  }
  printf "\n"
  next
}
{
  if ($0 ~ /^#/ || NF<1) next
  key=$1
  if (!(key in keys)) next   # only keys present in A (change to union if desired)

  # For each series name, read from A,B either (Re_x,Im_x) or literal x
  printf "%s", key
  for (si=1; si<=nS; si++){
    nm=series[si]
    # A values
    reA=imA=reB=imB=0
    if (("Re_" nm) in idxA && ("Im_" nm) in idxA) {
      reA = (rowA[key, idxA["Re_" nm]]+0)
      imA = (rowA[key, idxA["Im_" nm]]+0)
    } else if (nm in idxA) {
      split(parse_c(rowA[key, idxA[nm]]), zz, ",")
      reA=zz[1]+0; imA=zz[2]+0
    }
    # B values
    if (("Re_" nm) in idxB && ("Im_" nm) in idxB) {
      reB = ($idxB["Re_" nm]+0)
      imB = ($idxB["Im_" nm]+0)
    } else if (nm in idxB) {
      split(parse_c($idxB[nm]), zz2, ",")
      reB=zz2[1]+0; imB=zz2[2]+0
    }
    # central & sigma (two-run SEM proxy = |Δ|/2)
    c_re=(reA+reB)/2.0; c_im=(imA+imB)/2.0
    s_re=((reA-reB)>=0?(reA-reB):-(reA-reB))/2.0
    s_im=((imA-imB)>=0?(imA-imB):-(imA-imB))/2.0
    abs_c = sqrt(c_re*c_re + c_im*c_im)
    # first order propagate sigma_abs from component sigmas
    sigma_abs = (abs_c>0 ? (c_re/abs_c)*s_re + (c_im/abs_c)*s_im : (s_re+s_im)/sqrt(2))
    if (sigma_abs<0) sigma_abs=-sigma_abs
    printf "\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g\t%.16g", c_re, c_im, s_re, s_im, abs_c, sigma_abs
  }
  printf "\n"
}' "$A" "$B" > "$OUT"

# Merkle receipt (recompute root from canonicalized JSON)
python - "$OUT" <<'PY'
import json,sys,hashlib,os
out=sys.argv[1]
rec="tsv/elliptic_pass2_receipt.json"
try:
    d=json.load(open(rec,encoding="utf-8"))
except FileNotFoundError:
    d={}
arts=d.setdefault("artifacts",{})
# record/refresh artifact sha
sha=open(out,"rb").read()
art_sha=hashlib.sha256(sha).hexdigest()
arts["q1_central_sigma_tsv"]={"path":out,"sha256":art_sha,"uncertainty":"two-run SEM (|Δ|/2)"}
# canonicalize *without* merkle_root, then insert real root
canon=json.dumps({k:v for k,v in d.items() if k!="merkle_root"},
                 sort_keys=True,separators=(",",":"),ensure_ascii=False).encode()
d["merkle_root"]=hashlib.sha256(canon).hexdigest()
open(rec,"w",encoding="utf-8").write(json.dumps(d,indent=2,ensure_ascii=False)+"\n")
print(d["merkle_root"])
PY
