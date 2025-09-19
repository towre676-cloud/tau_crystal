#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: proof_tree.sh add <label> <rid> [parent_rid_csv]
cmd="${1:-}"; label="${2:-}"; rid="${3:-}"; parents="${4:-}"
LOG=".tau_ledger/geom/proof_tree.jsonl"; mkdir -p ".tau_ledger/geom"
case "$cmd" in
  add)
    [ -n "$label" ] && [ -n "$rid" ] || { echo "usage"; exit 2; }
    TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
    printf "%s\n" "{\"ts\":\"$TS\",\"label\":\"$label\",\"rid\":\"$rid\",\"parents\":\"$parents\"}" >> "$LOG"
    echo "$LOG" ;;
  *) echo "unknown"; exit 2 ;;
esac
