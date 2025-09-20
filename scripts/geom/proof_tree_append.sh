#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
op="$1"; fileA="$2"; fileB="$3"; param="$4"; value="$5"; thr="$6"; result="$7"
[ -f "$fileA" ] || fileA="/dev/null"
[ -f "$fileB" ] || fileB="/dev/null"
ah=$( ( [ -f "$fileA" ] && cat "$fileA" ) | (sha256sum 2>/dev/null || shasum -a 256 2>/dev/null || openssl dgst -sha256 -r) | awk "{print \$1}" )
bh=$( ( [ -f "$fileB" ] && cat "$fileB" ) | (sha256sum 2>/dev/null || shasum -a 256 2>/dev/null || openssl dgst -sha256 -r) | awk "{print \$1}" )
stamp=$(scripts/crypto/sha256_stamp.sh "$op|$ah|$bh|$param|$value|$thr|$result")
rid=$(printf "%s" "$stamp" | awk "{print \$1}")
ts=$(printf "%s" "$stamp" | awk "{print \$2}")
id=$(printf "%s" "$rid" | cut -c1-12)
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$id" "$ts" "$op" "$ah" "$bh" "$param" "$value" "$thr" "$result" "$rid" >> analysis/geom/proof_tree.tsv
echo "$rid"
