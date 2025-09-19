#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# judge.sh <receipts_dir>  — emits analysis/geom/proof.dot and transcript.tsv
DIR="${1:-.tau_ledger/geom}"
[ -d "$DIR" ] || { echo "[judge] no dir: $DIR"; exit 2; }
OUT_DOT="analysis/geom/proof.dot"; OUT_TSV="analysis/geom/transcript.tsv"
mkdir -p "$(dirname "$OUT_DOT")" "$(dirname "$OUT_TSV")"
: > "$OUT_DOT"; : > "$OUT_TSV"
printf "%s\n" "digraph G { rankdir=LR; node [shape=box,style=filled,fillcolor=lightgray]; }" > "$OUT_DOT"
printf "%s\n" "rid\tkind\tfile\taccept\tts\top_or_rule\tparam\thA\thB\trecalc_rid_ok\trecalc_hA_ok\trecalc_hB_ok" > "$OUT_TSV"
get_str(){ key="$1"; file="$2"; sed -n "s/.*\"${key}\"[[:space:]]*:[[:space:]]*\"\\([^\"]*\\)\".*/\\1/p" "$file" | head -n1; }
get_num(){ key="$1"; file="$2"; sed -n "s/.*\"${key}\"[[:space:]]*:[[:space:]]*\\([0-9][0-9]*\\).*/\\1/p" "$file" | head -n1; }
has_key(){ key="$1"; file="$2"; grep -q "\"$key\"" "$file"; }
dot_node(){ rid="$1"; label="$2"; acc="$3"; col="lightgray"; if [ "$acc" = "1" ]; then col="palegreen"; elif [ "$acc" = "0" ]; then col="lightcoral"; fi; esc_label=$(printf "%s" "$label" | sed "s/\"/\\\"/g"); echo "  \"$rid\" [label=\"$esc_label\", fillcolor=$col];" >> "$OUT_DOT"; }
dot_edge(){ from="$1"; to="$2"; echo "  \"$from\" -> \"$to\";" >> "$OUT_DOT"; }
declare -A FILE_BY_RID
declare -A ACC_BY_RID
declare -A LABEL_BY_RID
declare -A EDGES_FROM_PARENTS
shopt -s nullglob
for f in "$DIR"/*.json; do
  rid=$(get_str rid "$f")
  [ -n "$rid" ] || continue
  FILE_BY_RID["$rid"]="$f"
  acc=$(get_num accept "$f"); ACC_BY_RID["$rid"]="$acc"
  ts=$(get_str timestamp "$f"); [ -z "$ts" ] && ts=$(get_str ts "$f")
  if has_key op "$f"; then kind="op"; tag=$(get_str op "$f"); else kind="infer"; tag=$(get_str rule "$f"); fi
  param=$(get_str param "$f")
  hA=$(get_str hA "$f"); hB=$(get_str hB "$f")
  label="$tag\\n$(basename "$f")"
  LABEL_BY_RID["$rid"]="$label"
  dot_node "$rid" "$label" "$acc"
  # parents in infer receipts: ["path1","path2"]
  if has_key parents "$f"; then
    # extract quoted filenames inside array
    plist=$(sed -n "s/.*\"parents\"[[:space:]]*:[[:space:]]*\\[\\(.*\\)\\].*/\\1/p" "$f" | head -n1)
    # iterate each "something.json"
    echo "$plist" | tr "," "\n" | sed -n "s/.*\"\\([^\"]*\\)\".*/\\1/p" | while IFS= read -r p; do
      [ -n "$p" ] || continue
      # parent rid if file exists and contains rid
      if [ -s "$p" ]; then prid=$(get_str rid "$p"); [ -n "$prid" ] && EDGES_FROM_PARENTS["$prid:$rid"]=1; fi
    done
  fi
done
for rid in "${!FILE_BY_RID[@]}"; do
  f="${FILE_BY_RID[$rid]}"; acc="${ACC_BY_RID[$rid]}"; label="${LABEL_BY_RID[$rid]}"
  ts=$(get_str timestamp "$f"); [ -z "$ts" ] && ts=$(get_str ts "$f")
  salt=$(get_str salt "$f")
  if has_key op "$f"; then kind="op"; tag=$(get_str op "$f"); else kind="infer"; tag=$(get_str rule "$f"); fi
  param=$(get_str param "$f")
  hA=$(get_str hA "$f"); hB=$(get_str hB "$f")
  # optional future fields (if you update op.sh): a_path, b_path
  a_path=$(get_str a_path "$f"); b_path=$(get_str b_path "$f")
  recalc_hA=""; recalc_hB=""; recalc_rid=""
  if [ -n "$a_path" ] && [ -s "$a_path" ]; then ha2=$(sha256sum "$a_path" | awk "{print \$1}"); recalc_hA=$([ "$ha2" = "$hA" ] && echo "1" || echo "0"); fi
  if [ -n "$b_path" ] && [ -s "$b_path" ] && [ -n "$hB" ]; then hb2=$(sha256sum "$b_path" | awk "{print \$1}"); recalc_hB=$([ "$hb2" = "$hB" ] && echo "1" || echo "0"); fi
  if [ "$kind" = "op" ] && [ -n "$a_path" ]; then basis="$tag|$a_path|$b_path|$param|$ts|$salt"; rid2=$(printf "%s" "$basis" | sha256sum | awk "{print \$1}"); recalc_rid=$([ "$rid2" = "$rid" ] && echo "1" || echo "0"); fi
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$rid" "$kind" "$(basename "$f")" "${acc:-}" "${ts:-}" "${tag:-}" "${param:-}" "${hA:-}" "${hB:-}" "${recalc_rid:-}" "${recalc_hA:-}" "${recalc_hB:-}" >> "$OUT_TSV"
done
for k in "${!EDGES_FROM_PARENTS[@]}"; do from="${k%%:*}"; to="${k##*:}"; dot_edge "$from" "$to"; done
echo "[judge] wrote $OUT_TSV and $OUT_DOT"
