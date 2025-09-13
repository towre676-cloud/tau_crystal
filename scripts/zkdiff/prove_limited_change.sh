#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
base="${1:-}"; shift || true
[ -n "${base:-}" ] && [ -f "$base" ] || { echo "usage: $0 <base.files> <path1> [path2...]"; exit 2; }
declare -a claim=("$@")
sha(){ scripts/meta/_sha256.sh "$1"; }

# read baseline into arrays (portable parsing)
declare -A old; order=()
while IFS= read -r line; do
  # split at two spaces: "<hash>  <path>"
  h="${line%%  *}"
  p="${line#*  }"
  [ -n "$p" ] || continue
  old["$p"]="$h"
  order+=("$p")
done < "$base"

# extend with added files
for c in "${claim[@]}"; do
  if [ -z "${old[$c]:-}" ]; then
    old["$c"]="__MISSING__"
    order+=("$c")
  fi
done

# compute current hashes
declare -A new changed
for p in "${order[@]}"; do
  if [ -f "$p" ]; then nh="$(sha "$p")"; else nh="__MISSING__"; fi
  new["$p"]="$nh"
  [ "${old[$p]}" != "$nh" ] && changed["$p"]=1 || true
done

# set equality
declare -A claimset; for c in "${claim[@]:-}"; do claimset["$c"]=1; done
for p in "${!changed[@]}"; do [ -n "${claimset[$p]:-}" ] || { echo "[FAIL] extra change not claimed: $p"; exit 1; }; done
for p in "${!claimset[@]}"; do [ -n "${changed[$p]:-}" ] || { echo "[FAIL] claimed but unchanged: $p"; exit 1; }; done

# ladder from new state using baseline order (+ additions)
ladder=""
for p in "${order[@]}"; do
  ladder="$(printf '%s\n%s  %s' "$ladder" "${new[$p]}" "$p" | tr -d '\r' | sha256sum | awk '{print $1}')"
done

ts="$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)"
out=".tau_ledger/zkdiff/proof-$ts.proof"
: > "$out"
printf 'schema: %s\n' "taucrystal/zkdiff-proof/v1" >> "$out"
printf 'utc: %s\n' "$ts"                           >> "$out"
printf 'base_listing: %s\n' "$(basename "$base")"  >> "$out"
printf 'new_ladder_sha256: %s\n' "$ladder"         >> "$out"
printf 'changed_paths:' >> "$out"; for p in "${claim[@]}"; do printf ' %s' "$p" >> "$out"; done; printf '\n' >> "$out"
for p in "${claim[@]}"; do
  printf '  %s\n' "$p"               >> "$out"
  printf '    old: %s\n' "${old[$p]}" >> "$out"
  printf '    new: %s\n' "${new[$p]}" >> "$out"
done

man="docs/manifest.md"; tmp="docs/.manifest.zk.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
awk 'BEGIN{p=1} /^## zkdiff \(v1\)/{p=0} p{print}' "$man" >> "$tmp" 2>/dev/null || true
{
  printf '## zkdiff (v1)\n\n'
  printf 'proof: %s\n' "$(basename "$out")"
  printf 'new_ladder_sha256: %s\n\n' "$ladder"
} >> "$tmp"
mv "$tmp" "$man"
echo "[OK] proof @ $out (changed: ${#claim[@]}) new_ladder=$ladder"
