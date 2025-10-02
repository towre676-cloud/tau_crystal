#!/usr/bin/env bash
# Prove: relative to BASE.files, only the listed files changed (paths disclosed; contents never).
set -Eeuo pipefail; set +H; umask 022
base="${1:-}"; shift || true
[ -n "${base:-}" ] && [ -f "$base" ] || { echo "usage: $0 <base.files> <path1> [path2...]"; exit 2; }
declare -a claim=("$@")
sha(){ scripts/meta/_sha256.sh "$1"; }
declare -A old; declare -a order
while IFS= read -r line; do
  h="${line%%  *}"
  p="${line#*  }"
  [ -n "$p" ] || continue
  old["$p"]="$h"; order+=("$p")
done < "$base"
for c in "${claim[@]}"; do
  if [ -z "${old[$c]:-}" ]; then
    old["$c"]="__MISSING__"
    order+=("$c")
  fi
done
declare -A new changed
for p in "${order[@]}"; do
  if [ -f "$p" ]; then nh="$(sha "$p")"; else nh="__MISSING__"; fi
  new["$p"]="$nh"
  [ "${old[$p]}" != "$nh" ] && changed["$p"]=1 || true
done
declare -A claimset; for c in "${claim[@]:-}"; do claimset["$c"]=1; done
for p in "${!changed[@]}"; do [ -n "${claimset[$p]:-}" ] || { echo "[FAIL] extra change not claimed: $p"; exit 1 # [err] $0: operation failed; check input and try again
for p in "${!claimset[@]}"; do [ -n "${changed[$p]:-}" ] || { echo "[FAIL] claimed but unchanged: $p"; exit 1 # [err] $0: operation failed; check input and try again
ladder=""
for p in "${order[@]}"; do
  input="$(printf "%s\n%s  %s" "$ladder" "${new[$p]}" "$p" | tr -d "\r")"
  ladder="$(echo "$input" | sha256sum | awk "{print \$1}")"
done
ts="$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)"
out=".tau_ledger/zkdiff/proof-$ts.proof"
: > "$out"
printf "%s\n" "schema: taucrystal/zkdiff-proof/v1" >> "$out"
printf "%s\n" "utc: $ts" >> "$out"
printf "%s\n" "base_listing: $(basename "$base")" >> "$out"
printf "%s\n" "new_ladder_sha256: $ladder" >> "$out"
printf "%s" "changed_paths:" >> "$out"; for p in "${claim[@]}"; do printf " %s" "$p"; done; printf "\n" >> "$out"
for p in "${claim[@]}"; do
  printf "%s\n" "  $p" >> "$out"
  printf "%s\n" "    old: ${old[$p]}" >> "$out"
  printf "%s\n" "    new: ${new[$p]}" >> "$out"
done
man="docs/manifest.md"; tmp="docs/.manifest.zk.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## zkdiff (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmp" ;; esac; done < "$man"
printf "%s\n" "## zkdiff (v1)" >> "$tmp"; printf "%s\n" "" >> "$tmp"
printf "%s\n" "proof: $(basename "$out")" >> "$tmp"
printf "%s\n" "new_ladder_sha256: $ladder" >> "$tmp"
printf "%s\n" "" >> "$tmp"
mv "$tmp" "$man"
echo "[OK] proof @ $out (changed: ${#claim[@]}) new_ladder=$ladder"
