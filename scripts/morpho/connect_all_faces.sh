#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
echo "↪ reading dataset registry …"
missing=0; while IFS=$'\t' read -r DID DNAME DLIC DPATH DSTAT; do
  [ "$DID" = "id" ] && continue
  case "$DPATH" in "<PUT/"*|"" ) echo "• $DID pending (set path in registry)"; missing=$((missing+1)); continue ;; esac
  [ -f "$DPATH" ] && echo "• $DID OK: $DPATH" || { echo "• $DID MISSING: $DPATH"; missing=$((missing+1)); }
done < analysis/morpho/ref/datasets.registry.tsv
if [ "$missing" -gt 0 ]; then echo "NOTE: $missing dataset(s) not found yet — proceeding with available ones."; fi
scripts/morpho/ref_ingest.sh
scripts/morpho/ref_stats.sh
echo "✓ cohort ready. signature at analysis/morpho/ref/cohort.signature.tsv"
