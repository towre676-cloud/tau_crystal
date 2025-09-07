#!/usr/bin/env bash
set -euo pipefail
repo="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$repo"

outdir=".tau_ledger"; mkdir -p "$outdir"
stamp="$(date -u +%Y%m%dT%H%M%SZ)"
tsv="$outdir/assumptions-$stamp.tsv"
ndj="$outdir/assumptions-$stamp.ndjson"

: >"$tsv"; : >"$ndj"

git ls-files -z -- "*.lean" | while IFS= read -r -d '' f; do
  awk -v F="$f" '
    BEGIN{ nl=0 }
    {
      nl++
      # strip UTF-8 BOM on first line (octal: EF BB BF)
      if (NR==1) sub(/^\357\273\277/, "")
      # strip trailing Lean EOL comment
      sub(/[[:space:]]--.*$/, "")
      if ($0 ~ /^[[:space:]]*axiom[[:space:]]+[A-Za-z0-9_]+/) {
        match($0,/^[[:space:]]*axiom[[:space:]]+([A-Za-z0-9_]+)/,m)
        printf("axiom\t%s\t%s\t%d\n", m[1], F, nl)
      }
      if ($0 ~ /^[[:space:]]*opaque[[:space:]]+[A-Za-z0-9_]+/) {
        match($0,/^[[:space:]]*opaque[[:space:]]+([A-Za-z0-9_]+)/,m)
        printf("opaque\t%s\t%s\t%d\n", m[1], F, nl)
      }
      if ($0 ~ /^[[:space:]]*unsafe[[:space:]]+(def|theorem|abbrev|inductive|structure)[[:space:]]+[A-Za-z0-9_]+/) {
        match($0,/^[[:space:]]*unsafe[[:space:]]+(def|theorem|abbrev|inductive|structure)[[:space:]]+([A-Za-z0-9_]+)/,m)
        printf("unsafe\t%s\t%s\t%d\n", m[2], F, nl)
      }
    }
  ' < "$f"
done | while IFS=$'\t' read -r k n f l; do
  printf '%s\t%s\t%s\t%s\n' "$k" "$n" "$f" "$l" >>"$tsv"
  printf '{"kind":"%s","name":"%s","file":"%s","line":%s}\n' "$k" "$n" "$f" "$l" >>"$ndj"
done

cp -f "$tsv" "$outdir/assumptions.tsv"
cp -f "$ndj" "$outdir/assumptions.ndjson"

echo "[ok] boundary audit: $(wc -l < "$tsv") entries -> $tsv"
