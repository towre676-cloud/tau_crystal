#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -eu; umask 022; export LC_ALL=C LANG=C

# -------- config / args --------
SIGMA="2.5"                         # Nσ for outlier flagging
PATH_GLOB=""                        # optional: restrict scanned files (e.g. './.tau_ledger/entropy/witness_*.json')
SAMPLE_THRESHOLD=$((5*1024*1024))   # bytes; if file > threshold, sample instead of full
SAMPLE_CHUNK=$((256*1024))          # bytes from head and tail (total sample ~2*chunk)

usage() {
  cat <<USAGE
usage: $0 [--sigma N] [--path-glob GLOB] [--sample-threshold BYTES] [--sample-chunk BYTES]
defaults: --sigma $SIGMA  --sample-threshold $SAMPLE_THRESHOLD  --sample-chunk $SAMPLE_CHUNK
example: $0 --path-glob './.tau_ledger/entropy/witness_*.json'
USAGE
}

while [ $# -gt 0 ]; do
  case "$1" in
    --sigma)             SIGMA="$2"; shift 2;;
    --path-glob)         PATH_GLOB="$2"; shift 2;;
    --sample-threshold)  SAMPLE_THRESHOLD="$2"; shift 2;;
    --sample-chunk)      SAMPLE_CHUNK="$2"; shift 2;;
    -h|--help)           usage; exit 0;;
    *) echo "[err] unknown arg: $1"; usage; exit 2;;
  esac
done

OUTDIR_CSV="analysis/entropy"
OUTDIR_LEDGER=".tau_ledger/entropy"
mkdir -p "$OUTDIR_CSV" "$OUTDIR_LEDGER"

ts="$(date -u +%FT%TZ)"
OUTCSV="$OUTDIR_CSV/witness_scores.csv"
TMPCSV=".tmp.witness_scores.$$"
SUM="$OUTDIR_LEDGER/${ts//:/-}_witness_entropy.json"

# tools
have_gz=false;  command -v gzip   >/dev/null 2>&1 && have_gz=true
have_xz=false;  command -v xz     >/dev/null 2>&1 && have_xz=true
have_bz=false;  command -v bzip2  >/dev/null 2>&1 && have_bz=true
have_od=false;  command -v od     >/dev/null 2>&1 && have_od=true
have_hex=false; command -v hexdump>/dev/null 2>&1 && have_hex=true
command -v openssl  >/dev/null 2>&1 || { echo "[err] openssl not found"; exit 6; }
command -v awk      >/dev/null 2>&1 || { echo "[err] awk not found";     exit 5; }
command -v head     >/dev/null 2>&1 || { echo "[err] head not found";    exit 5; }
command -v tail     >/dev/null 2>&1 || { echo "[err] tail not found";    exit 5; }

# gather files (robust; no process substitution)
LIST=".tmp.witness_list.$$"; : > "$LIST"
if [ -n "$PATH_GLOB" ]; then
  # Use find with -path to respect the glob literally (quote the glob when calling the script!)
  find . -type f -path "$PATH_GLOB" 2>/dev/null | LC_ALL=C sort > "$LIST" || true
else
  find .tau_ledger -type f \( -name 'witness*.json' -o -name 'witness_*.json' \) 2>/dev/null | LC_ALL=C sort > "$LIST" || true
fi

# header for tmp (we'll add flags later)
: > "$TMPCSV"
printf '%s\n' 'file,bytes,sampled,sample_bytes,gz_bytes,xz_bytes,bz2_bytes,cr_gz,cr_xz,cr_bz2,bits_per_byte_gz,H8_est' >> "$TMPCSV"

# ---- helpers ----
make_sample() {
  # $1=file  $2=outpath  stdout: nothing; returns 0 if sample created (or full copy), 1 on error
  f="$1"; out="$2"
  sz=$(wc -c <"$f" | tr -d '[:space:]' || echo 0)
  if [ "$sz" -le 0 ]; then return 1; fi
  if [ "$sz" -le "$SAMPLE_THRESHOLD" ]; then
    # use full file
    cp -f "$f" "$out" || return 1
    echo "$sz"
    return 0
  fi
  # big file: concatenate head and tail chunks
  : > "$out"
  head -c "$SAMPLE_CHUNK" "$f" >> "$out" 2>/dev/null || true
  tail -c "$SAMPLE_CHUNK" "$f" >> "$out" 2>/dev/null || true
  # report sample size used
  wc -c <"$out" | tr -d '[:space:]'
  return 0
}

h8_of_bytes() {
  # read bytes from stdin and compute H8 via awk
  if $have_od; then
    od -An -t u1 2>/dev/null
  elif $have_hex; then
    hexdump -v -e '/1 "%u\n"'
  else
    cat >/dev/null; echo ""; return 0
  fi
}

# ---- main pass: compute per-file metrics into TMPCSV ----
n_scored=0
while IFS= read -r f; do
  [ -n "$f" ] || continue
  [ -s "$f" ] || continue

  sz=$(wc -c <"$f" | tr -d '[:space:]'); [ "$sz" -gt 0 ] || continue
  tmpbin=".tmp.ent.bytes.$$"
  sample_bytes=$(make_sample "$f" "$tmpbin" || echo 0)
  [ -s "$tmpbin" ] || { rm -f "$tmpbin"; continue; }
  sampled="false"; [ "$sz" -gt "$SAMPLE_THRESHOLD" ] && sampled="true"

  gz_sz=""; xz_sz=""; bz_sz=""
  cr_gz=""; cr_xz=""; cr_bz=""
  bpb_gz=""

  if $have_gz; then
    gz_sz=$(gzip -c -9 "$tmpbin" | wc -c | tr -d '[:space:]')
    cr_gz=$(awk -v a="$gz_sz" -v b="$sample_bytes" 'BEGIN{printf("%.6f",(b>0)?a/b:0)}')
    bpb_gz=$(awk -v a="$gz_sz" -v b="$sample_bytes" 'BEGIN{printf("%.6f",(b>0)?(8.0*a)/b:0)}')
  fi
  if $have_xz; then
    xz_sz=$(xz -c -9e "$tmpbin" | wc -c | tr -d '[:space:]')
    cr_xz=$(awk -v a="$xz_sz" -v b="$sample_bytes" 'BEGIN{printf("%.6f",(b>0)?a/b:0)}')
  fi
  if $have_bz; then
    bz_sz=$(bzip2 -c -9 "$tmpbin" | wc -c | tr -d '[:space:]')
    cr_bz=$(awk -v a="$bz_sz" -v b="$sample_bytes" 'BEGIN{printf("%.6f",(b>0)?a/b:0)}')
  fi

  # H8 from sample bytes
  H8=$(h8_of_bytes < "$tmpbin" | tr -s ' \t' '\n' \
      | grep -E '^[0-9]+$' \
      | awk '{ c[$1]++; n++ } END{ if(n==0){print "0.000000"; exit} H=0; for(b in c){p=c[b]/n; if(p>0) H+=-p*log(p)/log(2)} printf("%.6f", H) }')

  rm -f "$tmpbin"

  printf '%s\n' "$(printf '%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s' \
    "$f" "$sz" "$sampled" "$sample_bytes" \
    "${gz_sz:-}" "${xz_sz:-}" "${bz_sz:-}" \
    "${cr_gz:-}" "${cr_xz:-}" "${cr_bz:-}" "${bpb_gz:-}" "$H8")" >> "$TMPCSV"

  n_scored=$((n_scored+1))
done < "$LIST"
rm -f "$LIST"

# ---- second pass: compute medians / stddevs and add flags column ----
# We compute medians (robust) and stdevs for cr_gz and H8_est, then flag > SIGMA sigma.
: > "$OUTCSV"
printf '%s\n' 'file,bytes,sampled,sample_bytes,gz_bytes,xz_bytes,bz2_bytes,cr_gz,cr_xz,cr_bz2,bits_per_byte_gz,H8_est,flags' >> "$OUTCSV"

awk -v SIGMA="$SIGMA" '
BEGIN{ FS=","; OFS="," }
NR==1{ next } # skip header
{
  rows[NR]=$0
  cr=$8; h=$12
  if (cr!="") { crs[++ncr]=cr+0 }
  if (h!="")  { h8s[++nh]=h+0 }
}
END{
  # helpers
  proc_sort = "LC_ALL=C sort -n"
  # medians
  for (i=1;i<=ncr;i++) print crs[i] | proc_sort; close(proc_sort, "to")
  while ((proc_sort | getline v) > 0) { ++kcr; scr[kcr]=v+0 } close(proc_sort)
  mcr = (kcr==0)? "": ((kcr%2)? scr[(kcr+1)/2] : (scr[kcr/2]+scr[kcr/2+1])/2)

  proc_sort = "LC_ALL=C sort -n"
  for (i=1;i<=nh;i++) print h8s[i] | proc_sort; close(proc_sort, "to")
  while ((proc_sort | getline v) > 0) { ++kh; sh8[kh]=v+0 } close(proc_sort)
  mh8 = (kh==0)? "": ((kh%2)? sh8[(kh+1)/2] : (sh8[kh/2]+sh8[kh/2+1])/2)

  # stdevs
  sum=0; for(i=1;i<=ncr;i++) sum+=crs[i]; mean=(ncr>0)? sum/ncr:0
  var=0; for(i=1;i<=ncr;i++){d=crs[i]-mean; var+=d*d} sdcr=(ncr>1)? sqrt(var/(ncr-1)):0

  sum=0; for(i=1;i<=nh;i++) sum+=h8s[i]; mean=(nh>0)? sum/nh:0
  var=0; for(i=1;i<=nh;i++){d=h8s[i]-mean; var+=d*d} sdh8=(nh>1)? sqrt(var/(nh-1)):0

  # emit with flags
  print "file,bytes,sampled,sample_bytes,gz_bytes,xz_bytes,bz2_bytes,cr_gz,cr_xz,cr_bz2,bits_per_byte_gz,H8_est,flags"
  for (ri=2; ri<=NR; ri++) {
    split(rows[ri], a, FS)
    cr=a[8]+0; h=a[12]+0
    flag=""
    if (a[8] != "" && sdcr>0 && mcr!="") {
      if ( (cr - mcr) > SIGMA*sdcr || (mcr - cr) > SIGMA*sdcr ) flag=(flag==""?"CR_outlier":flag"|CR_outlier")
    }
    if (a[12] != "" && sdh8>0 && mh8!="") {
      if ( (h - mh8) > SIGMA*sdh8 || (mh8 - h) > SIGMA*sdh8 ) flag=(flag==""?"H8_outlier":flag"|H8_outlier")
    }
    print rows[ri], flag
  }
}
' "$TMPCSV" >> "$OUTCSV"

rm -f "$TMPCSV"

# ---- summary receipt ----
: > "$SUM"
printf '%s' "{" >> "$SUM"
printf '%s' "\"ts\":\"$ts\"," >> "$SUM"
printf '%s' "\"files_scored\":$n_scored," >> "$SUM"
printf '%s' "\"csv\":\"$OUTCSV\"," >> "$SUM"
printf '%s' "\"sigma\":$SIGMA," >> "$SUM"
printf '%s' "\"sample\":{ \"threshold\":$SAMPLE_THRESHOLD, \"chunk\":$SAMPLE_CHUNK }," >> "$SUM"
printf '%s' "\"path_glob\":\"$(printf '%s' "$PATH_GLOB" | sed 's/\"/'\''/g')\"," >> "$SUM"
printf '%s' "\"tools\":{\"gzip\":$($have_gz && echo true || echo false),\"xz\":$($have_xz && echo true || echo false),\"bzip2\":$($have_bz && echo true || echo false),\"od\":$($have_od && echo true || echo false),\"hexdump\":$($have_hex && echo true || echo false)}}" >> "$SUM"

echo "[ok] entropy scores → $OUTCSV ; summary → $SUM (files=$n_scored; σ=$SIGMA)"
