#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
A_anchor="$1"; B_target="$2"; tau="${3:-0.03}"
[ -f "$A_anchor" ] && [ -f "$B_target" ] || { echo "usage: A_anchor.tsv B_target.tsv [tau]" >&2; exit 1; }
S=$(scripts/geom/similarity_tau.sh "$A_anchor" "$B_target" "$tau")
ok=$(printf "%s" "$S" | awk "{print \$1}")
val=$(printf "%s" "$S" | awk "{print \$2}")
res="$ok"
rid=$(scripts/geom/proof_tree_append.sh "VERIFY" "$A_anchor" "$B_target" "tau" "$val" "$tau" "$res")
printf "%s\t%s\n" "$res" "$rid"
