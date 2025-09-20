#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
mkdir -p .tau_ledger
# Demo: fabricate two transcript stubs from existing manifests; replace with real run pickers
aid="tau_tanh_demo_A"; bid="tau_tanh_demo_B"
aenv="runner-A@toolchain-1"; benv="runner-B@toolchain-1"
aroot=$(printf "%s" "$aid$aenv" | sha256sum | awk "{print \\$1}")
broot=$(printf "%s" "$bid$benv" | sha256sum | awk "{print \\$1}")
atau=42; btau=41
A=".tau_ledger/last_run_A.json"; B=".tau_ledger/last_run_B.json"
: > "$A"; : > "$B"
printf "{\n  \x22id\x22: \x22%s\x22,\n  \x22root\x22: \x22%s\x22,\n  \x22env\x22: \x22%s\x22,\n  \x22tau\x22: %s\n}\n" "$aid" "$aroot" "$aenv" "$atau" >> "$A"
printf "{\n  \x22id\x22: \x22%s\x22,\n  \x22root\x22: \x22%s\x22,\n  \x22env\x22: \x22%s\x22,\n  \x22tau\x22: %s\n}\n" "$bid" "$broot" "$benv" "$btau" >> "$B"
scripts/coho/launch_cohom_verifiers.sh "$A" "$B"
