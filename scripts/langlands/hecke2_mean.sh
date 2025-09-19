#!/usr/bin/env bash
# optional key filter: only lines matching KEY_RX are considered before number extraction
KEY_RX="${KEY_RX:-tau|signature|l_tau}"

find "$D" -type f -name '*.json' -print0 2>/dev/null |
while IFS= read -r -d '' f; do
  # prefilter lines by key, strip CR
  if [ -n "$KEY_RX" ]; then
    pf() { grep -Ei "$KEY_RX" "$f" 2>/dev/null | tr -d '\r'; }
  else
    pf() { tr -d '\r' < "$f"; }
  fi
  # extract only 0.xxx or 1.000... tokens from prefiltered text
  pf | grep -Eo '0\.[0-9]+' >> "$raw" || true
  pf | grep -Eo '1\.0+'      >> "$raw" || true
done
# Convert to micro and clamp to [0, 1_200_000] just in case
while IFS= read -r x; do
  [ -z "${x:-}" ] && continue
  m="$(dec_to_micro "$x" 2>/dev/null || echo 0)"
  m=$((10#${m}))
  [ "$m" -ge 0 ] && [ "$m" -le 1200000 ] && printf '%d\n' "$m" >> "$vals"
done < "$raw"

N="$(wc -l < "$vals" 2>/dev/null || echo 0)"
[ "$N" -gt 0 ] || { echo "0 0"; exit 0; }

sort -n "$vals" > "$tmp/sorted.txt"

# 3-point moving average (endpoints repeat center)
mapfile -t arr < "$tmp/sorted.txt"
n="${#arr[@]}"; sum=0
for ((i=0;i<n;i++)); do
  ci="${arr[i]}"; pi="${arr[i>0?i-1:i]}"; ni="${arr[i<n-1?i+1:i]}"
  ci=$((10#${ci})); pi=$((10#${pi})); ni=$((10#${ni}))
  avg=$(( (pi + ci + ni)/3 ))
  sum=$(( sum + avg ))
done

echo "$sum $n"
