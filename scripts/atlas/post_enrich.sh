#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/atlas/_jq_compat.sh

atlas_dir="analysis/atlas"
atlas_jsonl="$atlas_dir/atlas_hecke.jsonl"
: > "$atlas_jsonl"

# last consensus (optional)
consensus="unknown"
[ -s analysis/metrics/consensus.jsonl ] && consensus=$(tail -n1 analysis/metrics/consensus.jsonl | awk -F'"' '/verdict/ {print $4}')

# last mirror verdict (optional)
mirror="unknown"
[ -s analysis/metrics/mirror.jsonl ] && mirror=$(tail -n1 analysis/metrics/mirror.jsonl | awk -F'"' '/mirror_verdict/ {print $4}')

for leaf in $(find "$atlas_dir" -maxdepth 2 -name leaf.json | sort); do
  dir=$(dirname "$leaf")
  adv_count=$(ls "$dir"/adversarial-p*.json 2>/dev/null | wc -l | tr -d ' ')
  jq -c --arg consensus "$consensus" --arg mirror "$mirror" --argjson adv "$adv_count" '
    {
      label: .curve.label,
      conductor: .curve.conductor,
      a: '"$a_array_filter"',
      panel: {primes_evaluated:.panel.primes_evaluated, pmax:.panel.pmax, path:.panel.path},
      parity: (.parity // {root:"unknown"}),
      numerics: {stable:(.numerics.stable // false), L_half:(.numerics.L_half // null)},
      consensus_last: $consensus,
      mirror_ok: ($mirror=="pass"),
      adversarial_samples: $adv
    }' "$leaf" >> "$atlas_jsonl"
done
echo "[post] wrote $(wc -l < "$atlas_jsonl") rows to $atlas_jsonl"
