#!/usr/bin/env bash
set -euo pipefail; umask 022
mkdir -p .tau_ledger/vows
ts=$(date -u +%Y%m%dT%H%M%SZ)
out=".tau_ledger/vows/vows-$ts.tsv"
{
  echo -e "when\tarea\tvow\tstatus"
  echo -e "$ts\tlanglands\tFlip STRICT_NORM=1 once normalization idempotent\topen"
  echo -e "$ts\tcapsules\tCapsule each stabilized double-zero claim\topen"
  echo -e "$ts\tmorpho\tEnforce boundary.txt+sig on all packs in CI\topen"
  echo -e "$ts\tfermion\tGate CKM unitarity with tolerance 1e-6\topen"
  echo -e "$ts\tphasehead\tEnsure phase_next_latest.sha matches max phase digest\topen"
  echo -e "$ts\tlean\tAdd lake build + proof.ok receipt in CI\topen"
  echo -e "$ts\tinterf\tDefine rows.tsv schema + writer receipt\topen"
} > "$out"
ln -sf "$(basename "$out")" .tau_ledger/vows/latest.tsv
echo "[VOWS] wrote $out"
