#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

atlas_jsonl="analysis/atlas/atlas_hecke.jsonl"
: > "$atlas_jsonl"

while IFS=$'\t' read -r N LABEL A1 A2 A3 A4 A6; do
  # skip comments/blank
  [[ -z "${N// }" ]] && continue
  [[ "$N" =~ ^# ]] && continue

  bash scripts/atlas/build_curve.sh "$LABEL" "$N" "$A1" "$A2" "$A3" "$A4" "$A6" >/dev/null

  leaf="analysis/atlas/${LABEL}/leaf.json"
  panel="analysis/atlas/${LABEL}/ap.tsv"
  [ -s "$leaf" ] || { echo "[atlas] missing leaf for $LABEL" >&2; exit 4; }

  # flatten a small summary line for grep-able atlas
  jq -c --arg label "$LABEL" '
    {
      label:$label,
      conductor:.curve.conductor,
      a:.curve.a,
      checks:.checks,
      panel:{primes_evaluated:.panel.primes_evaluated, pmax:.panel.pmax, path:.panel.path}
    }' "$leaf" >> "$atlas_jsonl"

done < <(awk 'NF && $1 !~ /^#/{print $1"\t"$2"\t"$3"\t"$4"\t"$5"\t"$6"\t"$7}' scripts/atlas/curves_canonical.tsv)

echo "[atlas] wrote $(wc -l < "$atlas_jsonl") rows to $atlas_jsonl"
