#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -eu; umask 022; export LC_ALL=C LANG=C

# knobs
PATH_GLOB="${1:-}"                  # optional: './.tau_ledger/entropy/witness_*.json'
LIMIT="${2:-}"                      # optional: max files
CHUNK=$((32*1024))                  # 32 KiB head + 32 KiB tail
CSV="analysis/entropy/witness_quick.csv"
TS="$(date -u +%FT%TZ)"
SUM=".tau_ledger/entropy/${TS//:/-}_witness_quick.json"

command -v gzip >/dev/null 2>&1 || { echo "[err] gzip not found"; exit 5; }
command -v awk  >/dev/null 2>&1 || { echo "[err] awk not found";  exit 5; }
mkdir -p "$(dirname "$CSV")" "$(dirname "$SUM")"

# build file list
LIST=".tmp.wq.list.$$"; : > "$LIST"
if [ -n "$PATH_GLOB" ]; then
  find . -type f -path "$PATH_GLOB" 2>/dev/null | LC_ALL=C sort > "$LIST" || true
else
  find .tau_ledger -type f \( -name 'witness*.json' -o -name 'witness_*.json' \) 2>/dev/null | LC_ALL=C sort > "$LIST" || true
fi

# load already-scored (file,size) to skip
SEEN=".tmp.wq.seen.$$"; : > "$SEEN"
if [ -s "$CSV" ]; then
  # CSV header: file,bytes,sampled,sample_bytes,gz1_bytes,cr_gz1
  tail -n +2 "$CSV" | awk -F, '{print $1","$2}' > "$SEEN" || true
fi

# write header if new file
if [ ! -s "$CSV" ]; then
  : > "$CSV"
  printf '%s\n' 'file,bytes,sampled,sample_bytes,gz1_bytes,cr_gz1' >> "$CSV"
fi

processed=0; added=0
while IFS= read -r f; do
  [ -n "$f" ] && [ -s "$f" ] || continue
  sz=$(wc -c <"$f" | tr -d '[:space:]'); [ "$sz" -gt 0 ] || continue

  # incremental skip: same file with same size already present
  if grep -Fqx "$f,$sz" "$SEEN" 2>/dev/null; then
    processed=$((processed+1))
    continue
  fi

  # sampling: build temp sample (head+tail)
  tmp=".tmp.wq.bytes.$$"; : > "$tmp"
  if [ "$sz" -le $((2*CHUNK)) ]; then
    cp -f "$f" "$tmp"
    sample_bytes="$sz"; sampled="false"
  else
    head -c "$CHUNK" "$f" >> "$tmp" 2>/dev/null || true
    tail -c "$CHUNK" "$f" >> "$tmp" 2>/dev/null || true
    sample_bytes=$(wc -c <"$tmp" | tr -d '[:space:]')
    sampled="true"
  fi

  # fast compression: gzip -1
  gz1_bytes=$(gzip -c -1 "$tmp" | wc -c | tr -d '[:space:]')
  cr_gz1=$(awk -v a="$gz1_bytes" -v b="$sample_bytes" 'BEGIN{printf("%.6f",(b>0)?a/b:0)}')
  rm -f "$tmp"

  printf '%s\n' "$(printf '%s,%s,%s,%s,%s,%s' "$f" "$sz" "$sampled" "$sample_bytes" "$gz1_bytes" "$cr_gz1")" >> "$CSV"

  added=$((added+1))
  processed=$((processed+1))
  if [ -n "$LIMIT" ] && [ "$processed" -ge "$LIMIT" ]; then break; fi
done < "$LIST"

rm -f "$LIST" "$SEEN"

# summary receipt
: > "$SUM"
printf '%s' "{" >> "$SUM"
printf '%s' "\"ts\":\"$TS\"," >> "$SUM"
printf '%s' "\"csv\":\"$CSV\"," >> "$SUM"
printf '%s' "\"added\":$added," >> "$SUM"
printf '%s' "\"limit\":\"$LIMIT\"," >> "$SUM"
printf '%s' "\"glob\":\"$(printf '%s' "$PATH_GLOB" | sed 's/\"/'\''/g')\"}" >> "$SUM"

echo "[ok] quick entropy → $CSV ; summary → $SUM (added=$added)"
