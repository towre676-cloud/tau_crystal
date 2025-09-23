#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
C=".tau_ledger/CHAIN"; T=".tau_ledger/tmp"; P=".tau_ledger/sheaf.preimage"; O=".tau_ledger/sheaf.digest"
rm -f "$T" "$P" "$O"; scripts/meta/_normalize.sh "$C" "$T"
LC=$(wc -l < "$T" | tr -d " ")
STAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
echo "tau_sheaf_v1" > "$P"; echo "lines:$LC" >> "$P"; echo "stamp:$STAMP" >> "$P"
R="0"; i=0; while read -r h; do i=$((i+1)); echo -n "$R $h" > "$T.r"; R=$(scripts/meta/_sha256.sh "$T.r"); echo "r$i:$R" >> "$P"; done < "$T"
scripts/meta/_sha256.sh "$P" > "$O"; cat "$O"
