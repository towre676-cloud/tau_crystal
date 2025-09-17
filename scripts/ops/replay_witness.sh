#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
BIN="${TAU_VERIFY_BIN:-./tau_verify}"
PACK="${1:?usage: replay_witness.sh witness-*.tar.gz}"
[ -x "$BIN" ] || { echo "[replay] missing verifier: $BIN" >&2; exit 2; }
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
tar -xzf "$PACK" -C "$work"
"$BIN" "$work" >/dev/null

# Merkle from manifest (hex concat → sha256)
mapfile -t H < <(jq -r '.[].sha256' "$work/manifest.json")
[ "${#H[@]}" -gt 0 ] || { echo "[replay] empty manifest" >&2; exit 3; }
arr=("${H[@]}")
while [ "${#arr[@]}" -gt 1 ]; do
  next=(); i=0
  while [ $i -lt ${#arr[@]} ]; do
    a="${arr[$i]}"; b="${arr[$((i+1))]:-$a}"
    h=$(printf "%s%s" "$a" "$b" | { command -v sha256sum >/dev/null && sha256sum || shasum -a256; } | awk '{print $1}')
    next+=("$h"); i=$((i+2))
  done
  arr=("${next[@]}")
done
bash_root="${arr[0]}"
rec_root=$(jq -r '.merkle_root' "$work/receipt.json")
[ "$bash_root" = "$rec_root" ] || { echo "[replay] Merkle mismatch"; echo "  bash:    $bash_root"; echo "  receipt: $rec_root"; exit 4; }
echo "[replay] OK (rust+bash agree): $bash_root"
