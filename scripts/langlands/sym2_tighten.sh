#!/usr/bin/env bash
set -Eeuo pipefail; set +H
. scripts/langlands/_bash_math.sh

IN="${1:-analysis/sym2_candidates.tsv}"
OUT="${2:-analysis/sym2_candidates.tuned.tsv}"

RE_GAP_MIN="${RE_GAP_MIN:-0.06}"   # |Re-0.5| >= 0.06
IM_MIN="${IM_MIN:-5.0}"            # |Im|   >= 5.0
SCORE_MIN="${SCORE_MIN:-0}"        # optional (>=)

# convert to micro for integer math
RGµ="$(dec_to_micro "$RE_GAP_MIN")"
IMµ="$(dec_to_micro "$IM_MIN")"
SMµ="$(dec_to_micro "$SCORE_MIN")"

: > "$OUT"
[ -s "$IN" ] || { echo "[sym2] no input: $IN"; exit 0; }

# skip header if any (line with non-numeric first token)
while IFS= read -r line; do
  [ -z "${line:-}" ] && continue
  first="${line%%[	 ]*}"
  case "$first" in
    ''|*[!0-9.-]*) continue ;;  # header or junk
  esac
  # fields: Re Im score ...
  set -- $line
  Re="${1:-0}"; Im="${2:-0}"; Sc="${3:-0}"
  Reµ="$(dec_to_micro "$Re")"
  Imµ="$(dec_to_micro "$Im")"
  Scµ="$(dec_to_micro "$Sc")"
  # |Re-0.5| >= RGµ  AND  |Im| >= IMµ  AND  Sc >= SCORE_MIN
  Hµ=$(( Reµ - 500000 ))
  [ "$Hµ" -lt 0 ] && Hµ=$(( -Hµ ))
  A=$(( Hµ >= RGµ ? 1 : 0 ))
  B=$(( (Imµ<0?-Imµ:Imµ) >= IMµ ? 1 : 0 ))
  C=$(( Scµ >= SMµ ? 1 : 0 ))
  if [ $((A&B&C)) -eq 1 ]; then
    printf "%s\n" "$line" >> "$OUT"
  fi
done < "$IN"

echo "$OUT"
