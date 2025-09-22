#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
HITS="analysis/discovery_hits.tsv"; BEST="analysis/discovery_best.tsv"
[ -s "$HITS" ] || { echo "[promote] no hits"; exit 0; }
last=$(tail -n1 "$HITS")
score_last=$(awk -F'\t' "{print (\$5? \$5 : 0)}" <<<"$last")
height_last=$(awk -F'\t' "{print (\$6? \$6 : 999)}" <<<"$last")
if [ -s "$BEST" ]; then
  score_best=$(awk -F'\t' "END{print (\$5? \$5 : 0)}" "$BEST")
  height_best=$(awk -F'\t' "END{print (\$6? \$6 : 999)}" "$BEST")
  if [ "$score_last" -lt "$score_best" ] || { [ "$score_last" -eq "$score_best" ] && awk "BEGIN{exit !($height_last < $height_best)}"; }; then
    : # worse — do nothing
  else
    cp -f "$HITS" "$BEST"
  fi
else cp -f "$HITS" "$BEST"; fi
echo "[promote] best updated: $(tail -n1 "$BEST")"
