#!/usr/bin/env bash
set +e; set +H; umask 022
# Usage: build_morphism_map.sh src_leaf_tsv dst_leaf_tsv [mapping_pairs.tsv] > map.tsv
# TSV formats:
#   leaf TSV:  <tid>\t<leaf_id>\t<count>
#   map TSV :  <leaf_src>\t<leaf_dst> (one per row)
SRC="$1"; DST="$2"; MP="$3"
TMP=$(mktemp 2>/dev/null || echo ".maptmp")
awk '{src[$2]=$2} END{for(k in src) print k}' "$SRC" | sort > "$TMP.src"
awk '{dst[$2]=$2} END{for(k in dst) print k}' "$DST" | sort > "$TMP.dst"
: > "$TMP.map"
if [ -f "$MP" ]; then
  awk 'NF{print $1"\t"$2}' "$MP" >> "$TMP.map"
fi
# Identity matches for intersection that weren't provided
comm -12 "$TMP.src" "$TMP.dst" | awk '{print $1"\t"$1}' >> "$TMP.map"
sort -u "$TMP.map"
