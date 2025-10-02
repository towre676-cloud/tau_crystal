#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
scripts/exec_geom/invariants.sh >/dev/null
rep=.tau_ledger/exec_geom/latest.json
chi=$(awk -F: '/"chiB"/{gsub(/[ ,]/,""); sub(/"chiB"/,""); print $2}' "$rep" 2>/dev/null || echo 0)
einv=$(awk -F: '/"e_invariant"/{gsub(/[ ,]/,""); sub(/"e_invariant"/,""); print $2}' "$rep" 2>/dev/null || echo 0)
geom=$(awk -F: '/"geometry_class"/{sub(/^[^\"]*\"/ ,""); sub(/\".*/ ,""); print $0}' "$rep" 2>/dev/null | sed -n '1p' || true)
needs_finite_state=false
awk -v x="$chi" 'BEGIN{exit !(x>1e-12)}' && needs_finite_state=true || true
if [ "$needs_finite_state" = true ]; then
  if [ ! -f .exec_geom/cert/finite_state.ok ]; then
    echo "[GUARD] chi(B)>0 without finite-state certificate (.exec_geom/cert/finite_state.ok)." >&2
    exit 66
  fi
fi
if awk -v x="$chi" 'BEGIN{exit !(x<-1e-12)}'; then
  : # negative curvature approved; unique fibration regime
fi
if awk -v x="$chi" 'BEGIN{exit !(x>-1e-12 && x<1e-12)}'; then
  if ! awk -v e="$einv" 'BEGIN{exit (e<-1e-12 || e>1e-12)}'; then
    : # Euclidean with e≈0: strict cover-trivial regime; good
  else
    echo "[WARN] chi(B)=0 but e!=0 (nil geometry). Ensure central τ extension is logged." >&2
  fi
fi
echo "[GUARD] Execution Geometry policy satisfied: geom=$geom chi=$chi e=$einv"
