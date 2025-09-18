#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/atlas/_parity_numeric.sh

atlas_dir="analysis/atlas"
atlas_jsonl="$atlas_dir/atlas_hecke.jsonl"
mkdir -p "$atlas_dir"

# read last consensus status if present
consensus="unknown"
[ -s analysis/metrics/consensus.jsonl ] && consensus=$(tail -n1 analysis/metrics/consensus.jsonl | awk -F'"' '/"verdict"/{print $4}')

: > "$atlas_jsonl"
for leaf in $(find "$atlas_dir" -maxdepth 2 -name leaf.json | sort); do
  dir=$(dirname "$leaf")
  label=$(jq -r '.curve.label' "$leaf")
  N=$(jq -r '.curve.conductor' "$leaf")
  a1=$(jq -r '.curve.a[0]' "$leaf"); a2=$(jq -r '.curve.a[1]' "$leaf")
  a3=$(jq -r '.curve.a[2]' "$leaf"); a4=$(jq -r '.curve.a[3]' "$leaf"); a6=$(jq -r '.curve.a[4]' "$leaf")
  panel=$(jq -r '.panel.path' "$leaf")

  parity_json=$(compute_root_number_json "$N" "$a1" "$a2" "$a3" "$a4" "$a6")
  numeric_json=$(dual_scale_numerics_json "$panel")

  tmp="$dir/leaf.tmp.json"
  jq --argjson parity "$parity_json" --argjson num "$numeric_json" \
     '.parity=$parity | .numerics=$num' "$leaf" > "$tmp" && mv "$tmp" "$leaf"

  # write atlas line
  jq -c --arg label "$label" --arg consensus "$consensus" \
     '{label:$label,
       conductor:.curve.conductor,
       a:.curve.a,
       panel:{primes_evaluated:.panel.primes_evaluated,pmax:.panel.pmax,path:.panel.path},
       parity:.parity,
       numerics:{stable:.numerics.stable,L_half:.numerics.L_half},
       consensus_last:$consensus}' "$leaf" >> "$atlas_jsonl"
done

echo "[post] atlas enriched → $atlas_jsonl"
