#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root="${1:-$PWD}"
out_file="${2:-.tau_ledger/action_wrapper.sha256}"
# include the composite metadata and the entrypoints it references
candidates=(
  "$root/action.yml"
  "$root/scripts/spec_guard.sh"
  "$root/scripts/tau_verify.sh"
  "$root/scripts/tau_adapter.sh"
  "$root/scripts/tau_sweep.sh"
  "$root/scripts/tau_fuse.sh"
)
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
for f in "${candidates[@]}"; do
  if [ -s "$f" ]; then
    printf '### %s ###\n' "$f" >> "$tmp"
    cat "$f" >> "$tmp"
    printf '\n' >> "$tmp"
  fi
done
sha="$(sha256sum "$tmp" | awk '{print $1}')"
printf '%s\n' "$sha" | tee "$out_file"
# opportunistically annotate manifest/receipt if jq is present
if command -v jq >/dev/null 2>&1; then
  for j in tau-crystal-manifest.json .tau_ledger/receipt.json; do
    [ -s "$j" ] || continue
    tmpj="$(mktemp)"; jq --arg s "$sha" '.action_wrapper_sha=$s' "$j" > "$tmpj" && mv "$tmpj" "$j"
  done
fi
