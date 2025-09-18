#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

need(){ command -v "$1" >/dev/null 2>&1 || { echo "[lock] missing $1" >&2; exit 2; }; }
need jq

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

parse_ST() { # file -> "S\tT\tSEL_HASH"
  local f="$1" S T H
  S=$(grep -E '^[[:space:]]*S=' "$f" | tail -1 | sed 's/.*=//; s/[[:space:]]//g')
  T=$(grep -E '^[[:space:]]*T=' "$f" | tail -1 | sed 's/.*=//; s/[[:space:]]//g')
  H=$(grep -E '^[[:space:]]*SEL_HASH=' "$f" | tail -1 | sed 's/.*=//; s/[[:space:]]//g')
  printf "%s\t%s\t%s" "${S:-}" "${T:-}" "${H:-}"
}

emit_pair() {
  local bestf="$1" secondf="$2"
  [ -s "$bestf" ] && [ -s "$secondf" ] || { echo "[lock] missing env files"; exit 3; }

  local bS bT bH sS sT sH
  IFS=$'\t' read -r bS bT bH <<<"$(parse_ST "$bestf")"
  IFS=$'\t' read -r sS sT sH <<<"$(parse_ST "$secondf")"

  [ -n "$bS" ] && [ -n "$bT" ] && [ -n "$sS" ] && [ -n "$sT" ] || { echo "[lock] S/T missing"; exit 4; }

  # canonical selection hashes (over "S<TAB>T")
  local bSel sSel
  bSel=${bH:-$(hash_str "$(printf "%s\t%s" "$bS" "$bT")")}
  sSel=${sH:-$(hash_str "$(printf "%s\t%s" "$sS" "$sT")")}

  # file hashes too
  local bFile sFile
  bFile=$(sha256 "$bestf"); sFile=$(sha256 "$secondf")

  # canonical order: "best" must be lexicographically <= "second"
  local order_ok=1
  [ "$bSel" \< "$sSel" ] || [ "$bSel" = "$sSel" ] || order_ok=0

  # pair hash over the two selection hashes in the labeled order
  local pair_hash; pair_hash=$(hash_str "${bSel}:${sSel}")

  mkdir -p analysis
  jq -n \
    --arg best_file "$bestf" --arg second_file "$secondf" \
    --arg bS "$bS" --arg bT "$bT" --arg sS "$sS" --arg sT "$sT" \
    --arg bSel "$bSel" --arg sSel "$sSel" \
    --arg bFile "$bFile" --arg sFile "$sFile" \
    --arg pair "$pair_hash" \
    --argjson order_ok "$order_ok" \
    '{
      kind:"reciprocity_pair",
      best:{file:$best_file, S:$bS, T:$bT, sel_hash:$bSel, file_hash:$bFile},
      second:{file:$second_file, S:$sS, T:$sT, sel_hash:$sSel, file_hash:$sFile},
      pair_hash:$pair,
      canonical_order_ok:$order_ok
    }' > analysis/reciprocity_pair_receipt.json

  # append a one-line WITNESS_PAIR stamp to atlas JSONL
  mkdir -p analysis/atlas
  local atlas="analysis/atlas/atlas_hecke.jsonl"
  [ -f "$atlas" ] || : > "$atlas"
  jq -n \
    --arg pair "$pair_hash" \
    --arg best "$bestf" --arg second "$secondf" \
    --arg bSel "$bSel" --arg sSel "$sSel" \
    '{WITNESS_PAIR:{pair_hash:$pair, best:$best, second:$second, best_sel:$bSel, second_sel:$sSel}}' >> "$atlas"

  echo "[lock] minted analysis/reciprocity_pair_receipt.json (order_ok=$order_ok)"
}

emit_pair "analysis/reciprocity_best.env" "analysis/reciprocity_second.env"
