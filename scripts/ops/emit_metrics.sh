#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
J=".tau_ledger/metrics.jsonl"; ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
run="${GITHUB_RUN_ID:-$(hostname)}"; commit=$(git rev-parse --short HEAD)
line=$(tail -n1 .tau_ledger/CHAIN || true); hash=$(awk '{print $1}' <<<"$line"); recp=$(awk '{print $2}' <<<"$line")
if [ -s analysis/laurent_ring.tsv ]; then read -r Lr Li Lk Lq Lseed < <(tail -n1 analysis/laurent_ring.tsv); else Lr=null; Li=null; Lk=null; Lq=null; fi
if [ -s analysis/discovery_hits.tsv ]; then score=$(tail -n1 analysis/discovery_hits.tsv | awk -F'\t' '{print ($5?$5:0)}'); height=$(tail -n1 analysis/discovery_hits.tsv | awk -F'\t' '{print ($6?$6:0)}'); else score=0; height=0; fi
panic=$([ -f PANIC ] && echo true || echo false)
printf '{"ts":"%s","run":"%s","commit":"%s","chain_hash":"%s","receipt_path":"%s","laurent":{"re":%s,"im":%s,"K":%s,"q":%s},"discovery":{"score":%s,"height":%s},"panic":%s}\n' \
  "$ts" "$run" "$commit" "${hash:-}" "${recp:-}" "${Lr}" "${Li}" "${Lk}" "${Lq}" "${score}" "${height}" "${panic}" >> "$J"
echo "[metrics] wrote $(tail -n1 "$J" | wc -c | tr -d ' ') bytes"
