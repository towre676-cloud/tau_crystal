#!/usr/bin/env bash
set +H; umask 022
status=0; shopt -s nullglob
for m in .tau_ledger/**/*.json .tau_ledger/*.json receipts/**/*.json receipts/*.json docs/**/*.json; do
  [ -f "$m" ] || continue
  case "$m" in */calibration_bad/*) continue ;; esac
  schema=$(grep -o "\"schema\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$m" | head -n1 | sed -e "s/.*:\"//" -e "s/\"$//")
  case "$schema" in
    taucrystal/calibration/*)
      grep -q "\"choice\"[[:space:]]*:" "$m" || { echo "::error file=$m::missing choice"; status=1; }
      grep -q "\"provenance\"[[:space:]]*:" "$m" || { echo "::error file=$m::missing provenance"; status=1; }
      ;;
    taucrystal/receipt/*)
      grep -q "\"tau_class\"[[:space:]]*:" "$m" || { echo "::error file=$m::missing tau_class"; status=1; }
      grep -q "\"provenance\"[[:space:]]*:" "$m" || { echo "::error file=$m::missing provenance"; status=1; }
      ;;
    *) ;;
  esac
done
exit "$status"
