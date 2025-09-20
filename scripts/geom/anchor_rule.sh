#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A_t1="$1"; A_t2="$2"; eps="${3:-0.01}"; delta="${4:-0.02}"
[ -f "$A_t1" ] && [ -f "$A_t2" ] || { echo "usage: A_t1.tsv A_t2.tsv [eps] [delta]" >&2; exit 1; }
S=$(scripts/geom/stability_frobenius.sh "$A_t1" "$A_t2" "$delta")
s_ok=$(printf "%s" "$S" | awk "{print \$1}")
s_val=$(printf "%s" "$S" | awk "{print \$2}")
sym=$(scripts/geom/symmetry_epsilon.sh "$A_t1" "$A_t2" "$eps")
y_ok=$(printf "%s" "$sym" | awk "{print \$1}")
y_val=$(printf "%s" "$sym" | awk "{print \$2}")
res="FALSE"; if [ "$s_ok" = "TRUE" ] && [ "$y_ok" = "TRUE" ]; then res="TRUE"; fi
rid=$(scripts/geom/proof_tree_append.sh "ANCHOR" "$A_t1" "$A_t2" "eps,delta" "$y_val,$s_val" "$eps,$delta" "$res")
printf "%s\t%s\n" "$res" "$rid"
