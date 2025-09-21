#!/usr/bin/env bash
set +H; umask 022

REC=$(ls -1t .tau_ledger/faces/face-modcurve-*.tsv 2>/dev/null | head -n1)
[ -n "$REC" ] || { echo "[[score]] no faces receipt"; exit 0; }

OUT=".tau_ledger/discovery/face_scores-$(date -u +%Y%m%dT%H%M%SZ).tsv"
printf "subject\tharmony_v2\tlevel\tscore\n" > "$OUT"

# helpers
tsvget() { # tsvget <file> <key>
  f="$1"; k="$2"
  [ -s "$f" ] || { echo na; return; }
  awk -F'\t' -v K="$k" 'tolower($1)==tolower(K){print $2; exit}' "$f"
}

jget_level() { # jget_level <json>   -> prints first numeric level or 0
  f="$1"
  [ -s "$f" ] || { echo 0; return; }
  awk 'match($0, /"level"[[:space:]]*:[[:space:]]*([0-9]+)/, m){print m[1]; exit}' "$f"
  test $? -eq 0 || echo 0
}

# subjects from receipt (explicit + modcurve basenames), unique
SUBJ1=$(awk -F'\t' '$1=="subject"{print $2}' "$REC")
SUBJ2=$(awk -F'\t' '$1=="modcurve"{n=$2; sub(/^.*\//,"",n); sub(/\.json$/,"",n); print n}' "$REC")
ALL=$(printf "%s\n%s\n" "$SUBJ1" "$SUBJ2" | awk 'NF{seen[$0]++} END{for(k in seen) print k}')

for S in $ALL; do
  [ -n "$S" ] || continue
  IDX="analysis/morpho/index/$S.tsv"
  H=$(tsvget "$IDX" "harmony_v2"); [ -n "$H" ] || H=na

  MC=".tau_ledger/discovery/modcurves/$S.json"
  L=$(jget_level "$MC"); [[ "$L" =~ ^[0-9]+$ ]] || L=0

  # normalize and score
  HN=$(awk -v x="$H" 'BEGIN{if(x+0<=0){print 0}else{y=x/100.0; if(y<0)y=0; if(y>1)y=1; printf("%.6f",y)}}')
  LN=$(awk -v l="$L" 'BEGIN{if(l+0<=0){print 0}else{y=l/50.0;  if(y<0)y=0; if(y>1)y=1; printf("%.6f",y)}}')
  SC=$(awk -v a="$HN" -v b="$LN" 'BEGIN{s=a*b; printf("%.6f",s)}')

  printf "%s\t%s\t%s\t%s\n" "$S" "${H:-na}" "${L:-0}" "$SC" >> "$OUT"
done

# sort desc by score, keep header
{ read h; printf "%s\n" "$h"; sort -t$'\t' -k4,4gr; } < "$OUT" > "$OUT.sorted" && mv "$OUT.sorted" "$OUT"

echo "[[score]] wrote $OUT"
