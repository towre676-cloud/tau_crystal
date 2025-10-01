#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
CID="${1:?complex id}"; TERMS="${2:?comma-separated object ids}"; DIFFS="${3:?comma-separated morphism ids}"
DST="analysis/derived/complexes"; mkdir -p "$DST"; OUT="$DST/$CID.json"; : > "$OUT"
t="["; IFS=, read -r -a arr <<< "$TERMS"; for i in "${!arr[@]}"; do [ $i -gt 0 ] && t="$t,"; t="$t\"${arr[$i]}\""; done; t="$t]"
d="["; IFS=, read -r -a ar2 <<< "$DIFFS"; for i in "${!ar2[@]}"; do [ $i -gt 0 ] && d="$d,"; d="$d\"${ar2[$i]}\""; done; d="$d]"
scripts/derived/_json.sh "$OUT" id "$CID" terms "__RAW__$t" differentials "__RAW__$d"
echo "$OUT"
