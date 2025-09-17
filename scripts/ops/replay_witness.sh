#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

BIN="${TAU_VERIFY_BIN:-./tau_verify}"
PACK="${1:?usage: replay_witness.sh witness-*.tar.gz}"

[ -x "$BIN" ] || { echo "[replay] missing verifier: $BIN" >&2; exit 2; }

work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
tar -xzf "$PACK" -C "$work"

echo "[replay] tau_verify…"
"$BIN" "$work" >/dev/null

# Build Merkle from manifest JSON (ASCII-hex concatenation hashed with sha256)
mapfile -t H < <(jq -r '.[].sha256' "$work/manifest.json")
if [ "${#H[@]}" -eq 0 ]; then echo "[replay] empty manifest"; exit 2; fi

merkle_array=("${H[@]}")
while [ "${#merkle_array[@]}" -gt 1 ]; do
  next=()
  i=0
  while [ $i -lt ${#merkle_array[@]} ]; do
    a="${merkle_array[$i]}"; b="${merkle_array[$((i+1))]:-$a}"
    h=$(printf "%s%s" "$a" "$b" | { if command -v sha256sum >/dev/null; then sha256sum; else shasum -a256; fi; } | awk '{print $1}')
    next+=("$h"); i=$((i+2))
  done
  merkle_array=("${next[@]}")
done
merkle_bash="${merkle_array[0]}"
merkle_receipt=$(jq -r '.merkle_root' "$work/receipt.json")

if [ "$merkle_bash" != "$merkle_receipt" ]; then
  echo "[replay] Merkle mismatch"; echo "  bash:     $merkle_bash"; echo "  receipt:  $merkle_receipt"; exit 3
fi

echo "[replay] OK (rust+bash agree): $merkle_bash"
