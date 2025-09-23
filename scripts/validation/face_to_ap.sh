#!/usr/bin/env bash
set -euo pipefail; set +H
IN="$1"; ID="$2"; WORK="validation/work/$ID"; mkdir -p "$WORK"
R="$WORK/r.tsv"; CUR="$WORK/curve.tsv"; AP1="$WORK/a_p.tsv"; AN1="$WORK/a_n.tsv"; AP2="$WORK/a_p_pass2.tsv"
bash scripts/validation/landmarks_to_r_safe.sh "$IN" "$R"
bash scripts/validation/r_to_curve.sh "$R" "$CUR"
bash scripts/validation/count_ap.sh "$CUR" "$AP1" "$AN1"
bash scripts/validation/count_ap.sh "$CUR" "$AP2" "$WORK/a_n_pass2.tsv"
set +e; bash scripts/validation/checks.sh "$AP1" "$AN1" "$AP2"; OK=$?; set -e
read _A A < <(grep "^A	" "$CUR"); read _B B < <(grep "^B	" "$CUR")
RFLAT=$(tr "\n" " " < "$R" | tr "\t" " " | sed "s/  */ /g; s/ $//")
HASH=$(sha256sum "$AP1" | awk '{print $1}')
ROW="id=$ID|r=$RFLAT|A=$A|B=$B|hash_ap=$HASH|ok=$OK"
printf "%s\n" "$ROW" > "$WORK/row.txt"
echo "$WORK/row.txt"
