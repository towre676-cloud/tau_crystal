#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage:
#   infer.sh anchor <symmetry_receipt.json> <stability_receipt.json>
#   infer.sh verify <anchor_receipt.json> <similar_receipt.json>
rule="${1:-}"; R1="${2:-}"; R2="${3:-}"
[ -n "$rule" ] && [ -s "$R1" ] && [ -s "$R2" ] || { echo "usage"; exit 2; }
TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
salt="$(printf "%s" "$(hostname)-$$-$(date +%s)-$RANDOM" | sha256sum | awk "{print \$1}")"

# pull the first numeric "accept" in the JSON (jq-free, tolerant of spacing/ordering)
accept_of(){ sed -n 's/.*"accept"[[:space:]]*:[[:space:]]*\([0-9][0-9]*\).*/\1/p' "$1" | head -n1; }
acc1="$(accept_of "$R1")"; acc2="$(accept_of "$R2")"
# normalize to {0,1}
case "$acc1" in 1) ;; *) acc1=0 ;; esac
case "$acc2" in 1) ;; *) acc2=0 ;; esac

RID="$(printf "%s" "$rule|$R1|$R2|$TS|$salt" | sha256sum | awk "{print \$1}")"
OUT=".tau_ledger/geom/${rule}_$(printf "%s" "$TS" | tr -cd "0-9")_${RID}.json"
: > "$OUT"
case "$rule" in
  anchor)
    ok=$(( acc1==1 && acc2==1 ? 1 : 0 ))
    printf "%s" "{" >> "$OUT"
    printf "%s" "\"rule\":\"anchor\",\"ts\":\"$TS\",\"rid\":\"$RID\",\"accept\":$ok,\"parents\":[\"$R1\",\"$R2\"],\"salt\":\"$salt\"" >> "$OUT"
    printf "%s\n" "}" >> "$OUT"
    ;;
  verify)
    ok=$(( acc1==1 && acc2==1 ? 1 : 0 ))
    printf "%s" "{" >> "$OUT"
    printf "%s" "\"rule\":\"verify\",\"ts\":\"$TS\",\"rid\":\"$RID\",\"accept\":$ok,\"parents\":[\"$R1\",\"$R2\"],\"salt\":\"$salt\"" >> "$OUT"
    printf "%s\n" "}" >> "$OUT"
    ;;
  *) echo "unknown rule"; rm -f "$OUT"; exit 2 ;;
esac
scripts/geom/proof_tree.sh add "$rule" "$RID" "$(basename "$R1"),$(basename "$R2")" >/dev/null
printf "%s\n" "$OUT"
