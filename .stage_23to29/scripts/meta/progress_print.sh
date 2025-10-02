#!/usr/bin/env bash
set -euo pipefail; umask 022
f="analysis/progress.tsv"
[ -f "$f" ] || { echo "no progress table yet ($f)"; exit 0; }
# try column if present; otherwise cat
if command -v column >/dev/null 2>&1; then
  column -t -s $'\t' "$f"
else
  cat "$f"
fi

# post-fix capsules_verify via deterministic verifier
bash .tau_ledger/capsules/.progress_hook.sh || true
