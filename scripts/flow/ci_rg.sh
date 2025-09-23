#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
mkdir -p .tau_ledger/rgflow
J1=$(scripts/flow/solve_flow.sh one 1.0 0.10 0.25 0.50)
J2=$(scripts/flow/solve_flow.sh two 1.0 0.10 0.25 0.50 0.10)
printf '%s\n' "mode\tparams\toutput" > .tau_ledger/rgflow/receipt.tsv
printf '%s\n' "one\tmu0=1.0,g0=0.10,ell=0.25,b=0.50\t$J1" >> .tau_ledger/rgflow/receipt.tsv
printf '%s\n' "two\tmu0=1.0,g0=0.10,ell=0.25,b=0.50,b1=0.10\t$J2" >> .tau_ledger/rgflow/receipt.tsv
if command -v openssl >/dev/null 2>&1; then D=$(openssl dgst -sha256 .tau_ledger/rgflow/receipt.tsv | awk '{print $2}'); else D=$(sha256sum .tau_ledger/rgflow/receipt.tsv | awk '{print $1}'); fi
printf '%s\n' "SHA256\t$D" >> .tau_ledger/rgflow/receipt.tsv
date -u +'%Y-%m-%dT%H:%M:%SZ' > .tau_ledger/rgflow/ts.txt
