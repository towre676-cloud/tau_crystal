#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Usage: calibrate.sh <kind> <min> <max> <steps> [target_rate]
# kind ∈ {symmetry, stability, similar}
K="${1:-symmetry}"
MIN="${2:-0.0025}"
MAX="${3:-0.0500}"
STEPS="${4:-10}"
TARGET="${5:-0.90}"
DIR=".tau_ledger/geom"
[ -d "$DIR" ] || { echo "[cal] no receipts"; exit 2; }

TMP="$(mktemp)"; : > "$TMP"
for f in "$DIR"/*.json; do
  case "$K" in
    symmetry) grep -q "\"op\":\"symmetry\"" "$f" || continue ;;
    stability) grep -q "\"op\":\"stability\"" "$f" || continue ;;
    similar)  grep -q "\"op\":\"similar\""  "$f" || continue ;;
    *) echo "[cal] unknown kind: $K"; rm -f "$TMP"; exit 3 ;;
  esac
  A=$(sed -n "s/.*\"a_path\"[[:space:]]*:[[:space:]]*\"\\([^\"]*\\)\".*/\\1/p" "$f" | head -n1)
  B=$(sed -n "s/.*\"b_path\"[[:space:]]*:[[:space:]]*\"\\([^\"]*\\)\".*/\\1/p" "$f" | head -n1)
  [ -n "$A" ] && [ -s "$A" ] || continue
  case "$K" in symmetry|similar) [ -n "$B" ] && [ -s "$B" ] || continue ;; esac
  printf "%s\t%s\n" "$A" "$B" >> "$TMP"
done
[ -s "$TMP" ] || { echo "[cal] no usable pairs for $K (need a_path/b_path)"; rm -f "$TMP"; exit 4; }

stepf(){ awk -v a="$MIN" -v b="$MAX" -v n="$STEPS" 'BEGIN{for(i=0;i<=n;i++){x=a+(b-a)*i/n; printf("%.6f\n",x)}}'; }

best=""; bestdiff=2
stepf | while IFS= read -r TH; do
  tot=0; ok=0
  while IFS=$'\t' read -r A B; do
    case "$K" in
      symmetry) J=$(scripts/geom/predicates.sh symmetry "$A" "$B" "$TH") ;;
      stability) J=$(scripts/geom/predicates.sh stability "$A" "$B" "$TH") ;;
      similar)  J=$(scripts/geom/predicates.sh similar  "$A" "$B" "$TH") ;;
    esac
    AOK=$(printf "%s" "$J" | sed -n "s/.*\"accept\"[[:space:]]*:[[:space:]]*\\([0-9][0-9]*\\).*/\\1/p")
    [ "$AOK" = "1" ] && ok=$((ok+1))
    tot=$((tot+1))
  done < "$TMP"
  rate=$(awk -v o="$ok" -v t="$tot" 'BEGIN{if(t==0)print 0; else printf("%.4f", o/t)}')
  diff=$(awk -v r="$rate" -v T="$TARGET" 'BEGIN{d=r-T; if(d<0)d=-d; printf("%.6f", d)}')
  printf "%s\t%s\t%s\n" "$K" "$TH" "$rate"
  if awk -v d="$diff" -v b="$bestdiff" 'BEGIN{exit !(d<b)}'; then best="$TH"; bestdiff="$diff"; fi
done
echo "[cal] suggested threshold for $K (target $TARGET): $best"
rm -f "$TMP"
