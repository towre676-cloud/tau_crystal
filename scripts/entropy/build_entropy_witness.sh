#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
outdir=".tau_ledger/entropy"; mkdir -p "$outdir"
chain=".tau_ledger/CHAIN"; [ -f "$chain" ] || : > "$chain"
tmp="$outdir/.chain.norm"; scripts/meta/_normalize.sh "$chain" "$tmp"
stamp=$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ); id="entv1-$stamp"; json="$outdir/$id.json"; sha="$outdir/$id.sha256"; : > "$json"
lines=$(wc -l < "$tmp" | tr -d " ")
bytes=$(wc -c < "$tmp" | tr -d " ")
gzbytes=$(gzip -c "$tmp" 2>/dev/null | wc -c | tr -d " " || echo 0)
ratio_pm=0; [ "$bytes" -gt 0 ] && ratio_pm=$(( gzbytes*1000/bytes ))
head1=$(tail -n 1 "$tmp" 2>/dev/null || echo "")
head0=$(tail -n 2 "$tmp" 2>/dev/null | head -n 1 || echo "")
difftag="same"; [ -n "$head0" ] && [ "$head0" != "$head1" ] && difftag="changed"
tf_dir=".tau_ledger/timefolds"; tf_count=0; tf_bytes=0
if [ -d "$tf_dir" ]; then
  tf_count=$(ls -1 "$tf_dir"/tf-*.tar.gz 2>/dev/null | wc -l | tr -d " " || echo 0)
  # sum bytes of archives (portable; ignore errors)
  for a in "$tf_dir"/tf-*.tar.gz; do [ -f "$a" ] || continue; s=$(wc -c < "$a" | tr -d " "); tf_bytes=$(( tf_bytes + s )); done
fi
printf "%s" "{" >> "$json"
printf "%s" "\"schema\":\"taucrystal/entropy/v1\"," >> "$json"
printf "%s" "\"id\":\"$id\"," >> "$json"
printf "%s" "\"utc\":\"$stamp\"," >> "$json"
printf "%s" "\"chain\":{" >> "$json"
printf "%s" "\"lines\":$lines," >> "$json"
printf "%s" "\"bytes\":$bytes," >> "$json"
printf "%s" "\"gzip_bytes\":$gzbytes," >> "$json"
printf "%s" "\"gzip_ratio_per_mille\":$ratio_pm," >> "$json"
printf "%s" "\"head_change\":\"$difftag\"" >> "$json"
printf "%s" "}," >> "$json"
printf "%s" "\"timefolds\":{" >> "$json"
printf "%s" "\"archives\":$tf_count," >> "$json"
printf "%s" "\"bytes\":$tf_bytes" >> "$json"
printf "%s" "}" >> "$json"
printf "%s\n" "}" >> "$json"
scripts/meta/_sha256.sh "$json" > "$sha"
printf "%s\n" "$json"
