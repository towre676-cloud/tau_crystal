#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
label="${1:-default}"
root=".tau_ledger/timefolds"
stamp=$(date -u +"%Y%m%dT%H%M%SZ")
id="tf-${stamp}"
lst="$root/$id.files"; arc="$root/$id.tar.gz"; meta="$root/$id.meta"; : > "$lst"
# deterministic candidate set; tweak as needed to widen/narrow scope
test -d .lake/build && find .lake/build -type f -print || true
test -f lake-manifest.json && echo "lake-manifest.json" || true
test -f lean-toolchain && echo "lean-toolchain" || true
test -f docs/manifest.md && echo "docs/manifest.md" || true
test -f .tau_ledger/CHAIN && echo ".tau_ledger/CHAIN" || true
) | sed "/^$/d" | LC_ALL=C sort > "$lst"
# archive with stable ordering via -T; avoid including the archive itself
tar -czf "$arc" -T "$lst" 2>/dev/null || {
 # fallback: manual feed if tar -T unsupported
 rm -f "$arc"; while IFS= read -r f; do tar -rf "$root/$id.tar" "$f"; done < "$lst"; gzip -f "$root/$id.tar"; mv "$root/$id.tar.gz" "$arc"
}
h=$(scripts/meta/_sha256.sh "$arc")
sz=$(wc -c < "$arc" | tr -d " ")
cnt=$(wc -l < "$lst" | tr -d " ")
: > "$meta"
echo "id: $id" >> "$meta"
echo "label: $label" >> "$meta"
echo "utc: $stamp" >> "$meta"
echo "archive: $(basename "$arc")" >> "$meta"
echo "sha256: $h" >> "$meta"
echo "bytes: $sz" >> "$meta"
echo "files: $cnt" >> "$meta"
printf "%s\n" "$arc"
