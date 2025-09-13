#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
include_all="${1:-}"
sha(){ scripts/meta/_sha256.sh "$1"; }
outdir=".tau_ledger/zkdiff"; mkdir -p "$outdir"
ts="$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)"
base="$outdir/base-$ts.files"; meta="$outdir/base-$ts.meta"

if [ "$include_all" = "--all" ]; then
  git ls-files -z > /tmp/.zk1.$$ || true
  git ls-files -o --exclude-standard -z > /tmp/.zk2.$$ || true
  cat /tmp/.zk1.$$ /tmp/.zk2.$$ > /tmp/.zk.$$ || true
  rm -f /tmp/.zk1.$$ /tmp/.zk2.$$
else
  git ls-files -z > /tmp/.zk.$$
fi

: > "$base"
while IFS= read -r -d '' f; do
  [ -f "$f" ] || continue
  h="$(sha "$f")"
  printf '%s  %s\n' "$h" "$f" >> "$base"
done < /tmp/.zk.$$
rm -f /tmp/.zk.$$
LC_ALL=C sort -o "$base" "$base"

ladder=""
while IFS= read -r line; do
  # use sha256sum/shasum on the line text
  d="$(printf '%s\n%s' "$ladder" "$line" | tr -d '\r' | sha256sum | awk '{print $1}')"
  ladder="$d"
done < "$base"

cnt="$(wc -l < "$base" | tr -d ' ')"
: > "$meta"
printf 'schema: %s\n' "taucrystal/zkdiff-baseline/v1" >> "$meta"
printf 'utc: %s\n' "$ts"                              >> "$meta"
printf 'files: %s\n' "$cnt"                           >> "$meta"
printf 'ladder_sha256: %s\n' "$ladder"                >> "$meta"
printf 'listing: %s\n' "$(basename "$base")"          >> "$meta"

man="docs/manifest.md"; tmp="docs/.manifest.zk.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
awk 'BEGIN{p=1} /^## zkdiff \(v1\)/{p=0} p{print}' "$man" >> "$tmp" 2>/dev/null || true
{
  printf '## zkdiff (v1)\n\n'
  printf 'baseline_meta: %s\n' "$(basename "$meta")"
  printf 'baseline_ladder_sha256: %s\n\n' "$ladder"
} >> "$tmp"
mv "$tmp" "$man"
echo "[OK] baseline @ $base ($cnt files) ladder=$ladder"
