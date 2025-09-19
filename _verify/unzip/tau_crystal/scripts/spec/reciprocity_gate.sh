#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

sha256() {
  local f="$1"
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$f" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$f" | awk '{print $1}'
  else openssl dgst -sha256 "$f" | awk '{print $2}'; fi
}
hash_str() {
  if command -v sha256sum >/dev/null 2>&1; then printf "%s" "$1" | sha256sum | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then printf "%s" "$1" | shasum -a 256 | awk '{print $1}'
  else printf "%s" "$1" | openssl dgst -sha256 -binary | od -An -tx1 | tr -d ' \n'; fi
}
parse_ST(){ local f="$1" S T H
  S=$(grep -E '^[[:space:]]*S=' "$f" | tail -1 | sed 's/.*=//; s/[[:space:]]//g')
  T=$(grep -E '^[[:space:]]*T=' "$f" | tail -1 | sed 's/.*=//; s/[[:space:]]//g')
  H=$(grep -E '^[[:space:]]*SEL_HASH=' "$f" | tail -1 | sed 's/.*=//; s/[[:space:]]//g')
  printf "%s\t%s\t%s" "${S:-}" "${T:-}" "${H:-}"
}

best="analysis/reciprocity_best.env"
second="analysis/reciprocity_second.env"
[ -f "$best" ] && [ -f "$second" ] || { echo "[gate] missing env files"; exit 12; }

# Must be *tracked* in git (enters Merkle spine)
git ls-files --error-unmatch "$best" >/dev/null 2>&1 || { echo "[gate] $best is not tracked"; exit 13; }
git ls-files --error-unmatch "$second" >/dev/null 2>&1 || { echo "[gate] $second is not tracked"; exit 13; }

# Recompute selection + file hashes
IFS=$'\t' read -r bS bT bH <<<"$(parse_ST "$best")"
IFS=$'\t' read -r sS sT sH <<<"$(parse_ST "$second")"
[ -n "$bS" ] && [ -n "$bT" ] && [ -n "$sS" ] && [ -n "$sT" ] || { echo "[gate] S/T missing"; exit 14; }

bSelCalc=$(hash_str "$(printf "%s\t%s" "$bS" "$bT")")
sSelCalc=$(hash_str "$(printf "%s\t%s" "$sS" "$sT")")
[ -z "$bH" ] || [ "$bH" = "$bSelCalc" ] || { echo "[gate] best SEL_HASH mismatch"; exit 15; }
[ -z "$sH" ] || [ "$sH" = "$sSelCalc" ] || { echo "[gate] second SEL_HASH mismatch"; exit 15; }

bFile=$(sha256 "$best"); sFile=$(sha256 "$second")

# Load receipt and compare
r="analysis/reciprocity_pair_receipt.json"
[ -s "$r" ] || { echo "[gate] missing receipt $r"; exit 16; }

rec_bSel=$(jq -r '.best.sel_hash' "$r")
rec_sSel=$(jq -r '.second.sel_hash' "$r")
rec_bFile=$(jq -r '.best.file_hash' "$r")
rec_sFile=$(jq -r '.second.file_hash' "$r")
rec_order=$(jq -r '.canonical_order_ok' "$r")
rec_pair=$(jq -r '.pair_hash' "$r")

[ "$rec_bSel" = "$bSelCalc" ] || { echo "[gate] best sel_hash mismatch vs receipt"; exit 17; }
[ "$rec_sSel" = "$sSelCalc" ] || { echo "[gate] second sel_hash mismatch vs receipt"; exit 17; }
[ "$rec_bFile" = "$bFile" ]    || { echo "[gate] best file_hash mismatch vs receipt"; exit 17; }
[ "$rec_sFile" = "$sFile" ]    || { echo "[gate] second file_hash mismatch vs receipt"; exit 17; }

# Canonical order: best <= second in lexicographic sel hash
[ "$rec_order" = "true" ] || { echo "[gate] canonical order violated (swap attempt?)"; exit 18; }

pair_calc=$(hash_str "${bSelCalc}:${sSelCalc}")
[ "$pair_calc" = "$rec_pair" ] || { echo "[gate] pair_hash mismatch"; exit 19; }

echo "[gate] reciprocity pair locked and consistent"
