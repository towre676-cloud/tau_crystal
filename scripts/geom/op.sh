#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: op.sh <opname> <fileA> [fileB] [param]
OP="${1:-}"; A="${2:-}"; B="${3:-}"; P="${4:-}"
[ -n "$OP" ] && [ -n "$A" ] || { echo "usage"; exit 2; }
TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
hA="$(sha256sum "$A" 2>/dev/null | awk "{print \$1}")"; hB=""; [ -n "$B" ] && [ -s "$B" ] && hB="$(sha256sum "$B" | awk "{print \$1}")"
salt="$(printf "%s" "$(hostname)-$$-$(date +%s)-$RANDOM" | sha256sum | awk "{print \$1}")"
basis="$OP|$A|$B|$P|$TS|$salt"
RID="$(printf "%s" "$basis" | sha256sum | awk "{print \$1}")"
OUT=".tau_ledger/geom/${OP}_$(printf "%s" "$TS" | tr -cd "0-9")_${RID}.json"
mkdir -p ".tau_ledger/geom"
res=""; case "$OP" in
  symmetry) res=$(scripts/geom/predicates.sh symmetry "$A" "$B" "$P") ;;
  stability) res=$(scripts/geom/predicates.sh stability "$A" "$B" "$P") ;;
  similar)  res=$(scripts/geom/predicates.sh similar  "$A" "$B" "$P") ;;
  *) echo "unknown op"; exit 2 ;;
esac
top_accept=$(printf "%s" "$res" | sed -n "s/.*\"accept\"[[:space:]]*:[[:space:]]*\\([0-9][0-9]*\\).*/\\1/p")
: > "$OUT"
printf "%s" "{" >> "$OUT"
printf "%s" "\"op\":\"$OP\",\"timestamp\":\"$TS\",\"rid\":\"$RID\",\"salt\":\"$salt\"," >> "$OUT"
printf "%s" "\"accept\":${top_accept:-0}," >> "$OUT"
printf "%s" "\"hA\":\"$hA\"" >> "$OUT"
if [ -n "$hB" ]; then printf "%s" ",\"hB\":\"$hB\"" >> "$OUT"; fi
if [ -n "$P" ]; then printf "%s" ",\"param\":\"$P\"" >> "$OUT"; fi
printf "%s" ",\"a_path\":\"$A\"" >> "$OUT"
if [ -n "$B" ]; then printf "%s" ",\"b_path\":\"$B\"" >> "$OUT"; fi
printf "%s" ",\"result\":$res" >> "$OUT"
printf "%s\n" "}" >> "$OUT"
printf "%s\n" "$OUT"
