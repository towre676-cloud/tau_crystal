#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C

# Config
OUTCSV="analysis/entropy/witness_scores.csv"
ts="$(date -u +%FT%TZ)"
SUM=".tau_ledger/entropy/${ts//:/-}_witness_entropy.json"

mkdir -p "$(dirname "$OUTCSV")" ".tau_ledger/entropy"

# Find witnesses (adjust the glob if your naming differs)
mapfile -t W < <(find .tau_ledger -type f -name 'witness*.json' -o -name 'witness_*.json' 2>/dev/null | LC_ALL=C sort)

# Header
: > "$OUTCSV"
printf '%s\n' 'file,bytes,gz_bytes,xz_bytes,bz2_bytes,cr_gz,cr_xz,cr_bz2,bits_per_byte_gz,H8_est' >> "$OUTCSV"

# Tool presence
have_gz=false; command -v gzip >/dev/null 2>&1 && have_gz=true
have_xz=false; command -v xz   >/dev/null 2>&1 && have_xz=true
have_bz=false; command -v bzip2 >/dev/null 2>&1 && have_bz=true

# Byte-entropy estimator (H8) via AWK over byte histogram
h8_of_file() {
  local f="$1"
  # Use od for portability; strip CR; build freq table
  od -An -t u1 "$f" 2>/dev/null \
  | tr -s ' \t' '\n' \
  | grep -E '^[0-9]+$' \
  | awk '
    { c[$1]++; n++ }
    END{
      if(n==0){ print "0.000000"; exit }
      H=0.0
      for (b in c) {
        p=c[b]/n
        if (p>0) H += -p*log(p)/log(2)
      }
      printf("%.6f", H)
    }'
}

n_scored=0
for f in "${W[@]}"; do
  [ -s "$f" ] || continue
  sz=$(wc -c <"$f" | tr -d '[:space:]')
  [ "$sz" -gt 0 ] || continue

  gz_sz=; xz_sz=; bz_sz=
  cr_gz=; cr_xz=; cr_bz=
  bpb_gz=

  if $have_gz; then
    gz_sz=$(gzip -c -9 "$f" | wc -c | tr -d '[:space:]')
    cr_gz=$(awk -v a="$gz_sz" -v b="$sz" 'BEGIN{printf("%.6f", (b>0)? a/b : 0)}')
    bpb_gz=$(awk -v a="$gz_sz" -v b="$sz" 'BEGIN{printf("%.6f", (b>0)? (8.0*a)/b : 0)}')
  else
    gz_sz=""
    cr_gz=""
    bpb_gz=""
  fi

  if $have_xz; then
    xz_sz=$(xz -c -9e "$f" | wc -c | tr -d '[:space:]')
    cr_xz=$(awk -v a="$xz_sz" -v b="$sz" 'BEGIN{printf("%.6f", (b>0)? a/b : 0)}')
  else
    xz_sz=""
    cr_xz=""
  fi

  if $have_bz; then
    bz_sz=$(bzip2 -c -9 "$f" | wc -c | tr -d '[:space:]')
    cr_bz=$(awk -v a="$bz_sz" -v b="$sz" 'BEGIN{printf("%.6f", (b>0)? a/b : 0)}')
  else
    bz_sz=""
    cr_bz=""
  fi

  H8=$(h8_of_file "$f" || printf "0.000000")

  printf '%s\n' "$(printf '%s,%s,%s,%s,%s,%s,%s,%s,%s,%s' \
    "$f" "$sz" "${gz_sz:-}" "${xz_sz:-}" "${bz_sz:-}" \
    "${cr_gz:-}" "${cr_xz:-}" "${cr_bz:-}" "${bpb_gz:-}" "$H8")" >> "$OUTCSV"

  n_scored=$((n_scored+1))
done

# Emit summary JSON
: > "$SUM"
printf '%s' "{" >> "$SUM"
printf '%s' "\"ts\":\"$ts\"," >> "$SUM"
printf '%s' "\"files_scored\":$n_scored," >> "$SUM"
printf '%s' "\"csv\":\"$OUTCSV\"," >> "$SUM"
printf '%s' "\"tools\":{\"gzip\":$($have_gz && echo true || echo false),\"xz\":$($have_xz && echo true || echo false),\"bzip2\":$($have_bz && echo true || echo false)}}" >> "$SUM"

echo "[ok] entropy scores → $OUTCSV ; summary → $SUM"
