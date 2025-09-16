#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/receipts"
out=".tau_ledger/metrics/h1_cech.json"
mkdir -p "$(dirname "$out")"
shopt -s nullglob
files=("$root"/*.json)
if [ "${#files[@]}" -eq 0 ]; then echo "{\"H1\":0,\"vertices\":0,\"edges\":0}" > "$out"; echo "$out"; exit 0; fi
tmp_map="$(mktemp)"; : > "$tmp_map"
for r in "${files[@]}"; do
  # extract context_id without jq; fall back to UNKNOWN if not found
  cid=$(grep -o "\"context_id\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$r" 2>/dev/null | head -n1 | sed -E "s/.*:\"([^\"]*)\".*/\\1/")
  [ -n "${cid:-}" ] || cid="UNKNOWN"
  if command -v jq >/dev/null 2>&1; then norm=$(jq -S . "$r" 2>/dev/null | sha256sum | awk "{print \$1}"); else norm=$(openssl dgst -sha256 "$r" | awk "{print \$2}"); fi
  printf "%s\t%s\t%s\n" "$cid" "$norm" "$r" >> "$tmp_map"
done
verts=$(cut -f1 "$tmp_map" | sort -u | wc -l | awk "{print \$1}")
edges=0
while IFS=$'\n' read -r cid; do
  # count distinct digests within the same context_id
  dcount=$(awk -F'\t' -v k="$cid" '$1==k{print $2}' "$tmp_map" | sort -u | wc -l | awk "{print \$1}")
  if [ "$dcount" -gt 1 ]; then edges=$((edges + dcount - 1)); fi
done < <(cut -f1 "$tmp_map" | sort -u)
H1=0; if [ "$edges" -gt 0 ]; then H1=1; fi
printf "{\\"H1\\":%d,\\"vertices\\":%d,\\"edges\\":%d}\n" "$H1" "$verts" "$edges" > "$out"
rm -f "$tmp_map"; echo "$out"
