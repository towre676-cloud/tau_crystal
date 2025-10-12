#!/usr/bin/env bash
# tsv_add_header.sh <in.tsv> <out.tsv> — ensure header "u a a1 a2 p2 p1 p0 seed", normalize to tabs
set -euo pipefail; set +H; umask 022; export LC_ALL=C
IN="${1:?Usage: tsv_add_header.sh <in.tsv> <out.tsv>}"; OUT="${2:?}"
hdr=$'u\ta\ta1\ta2\tp2\tp1\tp0\tseed'
sed -i 's/\r$//' "$IN" 2>/dev/null || true
first="$(head -n1 "$IN")"
if printf '%s\n' "$first" | grep -qiE '(^|[[:space:]])u([[:space:]]|$)'; then
  # already has a header: rewrite rows with tab separators
  awk -v OFS='\t' 'NR==1{print; next}{for(i=1;i<=NF;i++) $i=$i; print}' "$IN" > "$OUT"
else
  { printf '%s\n' "$hdr"; cat "$IN"; } | awk -v OFS='\t' '{for(i=1;i<=NF;i++) $i=$i; print}' > "$OUT"
fi
