#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: op.sh <opname> <fileA> [fileB] [param]
OP="${1:-}"; A="${2:-}"; B="${3:-}"; P="${4:-}"
[ -n "$OP" ] && [ -n "$A" ] || { echo "usage"; exit 2; }

sh256() {
  f="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$f" 2>/dev/null | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$f" 2>/dev/null | awk '{print $1}'
  else
    echo ""
  fi
}

TS="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
hA=""; [ -s "$A" ] && hA="$(sh256 "$A")"
hB=""; [ -n "$B" ] && [ -s "$B" ] && hB="$(sh256 "$B")"
salt="$(printf "%s" "$(hostname)-$$-$(date +%s)-$RANDOM" | sh256 /dev/stdin)"
basis="$OP|$A|$B|$P|$TS|$salt"
RID="$(printf "%s" "$basis" | sh256 /dev/stdin)"
OUT=".tau_ledger/geom/${OP}_$(printf "%s" "$TS" | tr -cd "0-9")_${RID}.json"
mkdir -p ".tau_ledger/geom"

case "$OP" in
  symmetry) res=$(scripts/geom/predicates.sh symmetry "$A" "$B" "$P") ;;
  stability) res=$(scripts/geom/predicates.sh stability "$A" "$B" "$P") ;;
  similar)  res=$(scripts/geom/predicates.sh similar  "$A" "$B" "$P") ;;
  *) echo "unknown op"; exit 2 ;;
esac

# mirror accept:=1 if present in result JSON, else 0
if printf "%s" "$res" | tr -d "\r\n" | grep -q "\"accept\"[[:space:]]*:[[:space:]]*1"; then
  top_accept=1
else
  top_accept=0
fi

: > "$OUT"
printf "%s" "{" >> "$OUT"
printf "%s" "\"op\":\"$OP\",\"timestamp\":\"$TS\",\"rid\":\"$RID\",\"salt\":\"$salt\"," >> "$OUT"
printf "%s" "\"accept\":${top_accept}," >> "$OUT"
printf "%s" "\"hA\":\"$hA\"" >> "$OUT"
if [ -n "$hB" ]; then printf "%s" ",\"hB\":\"$hB\"" >> "$OUT"; fi
if [ -n "$P" ]; then printf "%s" ",\"param\":\"$P\"" >> "$OUT"; fi
printf "%s" ",\"a_path\":\"$A\"" >> "$OUT"
if [ -n "$B" ]; then printf "%s" ",\"b_path\":\"$B\"" >> "$OUT"; fi
printf "%s" ",\"result\":$res" >> "$OUT"
printf "%s\n" "}" >> "$OUT"
printf "%s\n" "$OUT"
