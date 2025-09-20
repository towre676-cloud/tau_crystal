#!/usr/bin/env bash
set +e; set +H; umask 022
. scripts/coho/lib_json.sh
# Usage: tau_cert_from_leaves.sh src_leaf_tsv dst_leaf_tsv per_leaf_tau.tsv LAMBDA > tau.tsv
# per_leaf_tau.tsv:  <leaf_id>\t<tau_int>
SRC="$1"; DST="$2"; TAU="$3"; LAMBDA="$4"; [ -n "$LAMBDA" ] || LAMBDA=0
awk '{t[$1]=$2} END{for(k in t) print k"\t"t[k]}' "$TAU" | sort > "$TAU.sorted"
join -a1 -e 0 -o 0,1.2,2.2 -t $'\t' <(sort -k2,2 "$SRC" | awk '{c[$2]+=$3} END{for(k in c) print k"\t"c[k]}') "$TAU.sorted" 2>/dev/null | awk '{print $1"\t"($2*$3)}' | awk '{s+=$2} END{print "tau_src\t"s}' > .tau_ledger/.tau_src.tmp
join -a1 -e 0 -o 0,1.2,2.2 -t $'\t' <(sort -k2,2 "$DST" | awk '{c[$2]+=$3} END{for(k in c) print k"\t"c[k]}') "$TAU.sorted" 2>/dev/null | awk '{print $1"\t"($2*$3)}' | awk '{s+=$2} END{print "tau_dst\t"s}' > .tau_ledger/.tau_dst.tmp
paste .tau_ledger/.tau_src.tmp .tau_ledger/.tau_dst.tmp | awk -v L="$LAMBDA" '{d=$2-$4; if(d<0)d=-d; printf "tau_src\t%s\n tau_dst\t%s\n tau_drift_abs\t%s\n lambda\t%s\n", $2,$4,d,L}' > .tau_ledger/tau_cert.tsv
cat .tau_ledger/tau_cert.tsv
