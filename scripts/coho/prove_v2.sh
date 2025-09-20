#!/usr/bin/env bash
set +e; set +H; umask 022
cd "$HOME/Desktop/tau_crystal/tau_crystal" || { echo "cd failed"; exit 1; }

DELTA=".tau_ledger/delta.tsv"
SRC=".tau_ledger/src_leaf.tsv"
DST=".tau_ledger/dst_leaf.tsv"
TAU=".tau_ledger/tau_cert.tsv"

for f in "$DELTA" "$SRC" "$DST" "$TAU"; do
  [ -f "$f" ] || { echo "::error::missing $f"; exit 1; }
done

echo "Preparing Lean (lake update)..."
if command -v lake >/dev/null 2>&1; then
  lake update || { echo "::error::lake update failed"; exit 1; }
  echo "Building Lean (default target)..."
  lake build   || { echo "::error::lake build failed"; exit 1; }
  echo "Running Lean verification..."
  lake exe prove_v2 "$DELTA" "$SRC" "$DST" "$TAU"
  exit $?
else
  echo "::warning::lake not found; mock verification"
  L1=$(awk '{v=$2; if(v<0)v=-v; s+=v} END{print s+0}' "$DELTA")
  TD=$(awk '$1=="tau_drift_abs"{print $2}' "$TAU")
  LB=$(awk '$1=="lambda"{print $2}' "$TAU")
  if [ "${L1:-0}" -eq 0 ] && [ "${TD:-0}" -eq 0 ]; then OK=true; MSG="VERIFIED (mock): Δ=0, τ conserved"
  elif [ "${TD:-0}" -le "$(( ${LB:-0} * ${L1:-0} ))" ]; then OK=true; MSG="VERIFIED (mock): |Δτ| ≤ λ‖Δ‖₁"
  else OK=false; MSG="FAILED (mock): |Δτ| > λ‖Δ‖₁"; fi
  cat > .tau_ledger/lean_proof_v2.json <<JSON
{
  "lean_proof_v2": {
    "verified": ${OK},
    "message": "${MSG}",
    "delta_l1_norm": ${L1:-0},
    "tau_drift_abs": ${TD:-0},
    "lambda": ${LB:-0},
    "mock": true
  }
}
JSON
  echo "$MSG"; [ "$OK" = true ]
fi
