#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
label="${1:-default}"
root=".tau_ledger/timefolds"
stamp=$(date -u +%Y%m%dT%H%M%SZ)
id="tf-${stamp}"
lst="$root/$id.files"; arc="$root/$id.tar.gz"; meta="$root/$id.meta"
: > "$lst.tmp"
[ -d .lake/build ] && find .lake/build -type f -print >> "$lst.tmp" || true
[ -f lake-manifest.json ] && echo "lake-manifest.json" >> "$lst.tmp" || true
[ -f lean-toolchain ] && echo "lean-toolchain" >> "$lst.tmp" || true
[ -f docs/manifest.md ] && echo "docs/manifest.md" >> "$lst.tmp" || true
[ -f .tau_ledger/CHAIN ] && echo ".tau_ledger/CHAIN" >> "$lst.tmp" || true
sed "/^$/d" "$lst.tmp" | LC_ALL=C sort > "$lst"; rm -f "$lst.tmp"
rm -f "$arc" "$root/$id.tar"
if tar -czf "$arc" -T "$lst" 2>/dev/null; then :; else while IFS= read -r f; do tar -rf "$root/$id.tar" "$f"; done < "$lst"; gzip -f "$root/$id.tar"; mv "$root/$id.tar.gz" "$arc"; fi
h=$(scripts/meta/_sha256.sh "$arc")
sz=$(wc -c < "$arc" | tr -d " ")
cnt=$(wc -l < "$lst" | tr -d " ")
: > "$meta"
printf "%s\n" "id: $id" >> "$meta"
printf "%s\n" "label: $label" >> "$meta"
printf "%s\n" "utc: $stamp" >> "$meta"
printf "%s\n" "archive: $(basename "$arc")" >> "$meta"
printf "%s\n" "sha256: $h" >> "$meta"
printf "%s\n" "bytes: $sz" >> "$meta"
printf "%s\n" "files: $cnt" >> "$meta"
