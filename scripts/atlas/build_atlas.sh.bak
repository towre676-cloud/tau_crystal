#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022

atlas_jsonl="analysis/atlas/atlas_hecke.jsonl"
: > "$atlas_jsonl"

total=$(awk 'NF && $1 !~ /^#/{c++} END{print c+0}' scripts/atlas/curves_canonical.tsv)
idx=0

while IFS=$'\t' read -r N LABEL A1 A2 A3 A4 A6; do
  [[ -z "${N// }" ]] && continue
  [[ "$N" =~ ^# ]] && continue

  idx=$((idx+1))
  echo "[atlas] processed $idx/$total: $LABEL (N=$N)"

  bash scripts/atlas/build_curve.sh "$LABEL" "$N" "$A1" "$A2" "$A3" "$A4" "$A6" >/dev/null

  leaf="analysis/atlas/${LABEL}/leaf.json"
  [ -s "$leaf" ] || { echo "[atlas] missing leaf for $LABEL" >&2; exit 4; }

  jq -c --arg label "$LABEL" '
    {
      label:$label,
      conductor:.curve.conductor,
      a:.curve.a,
      invariants:{delta:.invariants.delta},
      checks:{
        hasse:.checks.hasse,
        parity:.checks.parity
      },
      numerics:{
        Lhalf:.numerics.Lhalf, L1:.numerics.L1,
        two_scale_agree:.numerics.two_scale_agree,
        tail_proxy:.numerics.tail_proxy
      },
      panel:{primes_evaluated:.panel.primes_evaluated, pmax:.panel.pmax, path:.panel.path},
      flags:{
        hasse_ok:(.checks.hasse.violations==0),
        parity_computed:(.checks.parity.root_number!=null),
        candidate_central_zero:(.numerics.Lhalf!=null and (.numerics.Lhalf | tonumber) < (.numerics.tail_proxy.half | tonumber) and (.checks.parity.root_number==1))
      }
    }' "$leaf" >> "$atlas_jsonl"

done < <(awk 'NF && $1 !~ /^#/{print $1"\t"$2"\t"$3"\t"$4"\t"$5"\t"$6"\t"$7}' scripts/atlas/curves_canonical.tsv)

echo "[atlas] wrote $(wc -l < "$atlas_jsonl") rows to $atlas_jsonl"
