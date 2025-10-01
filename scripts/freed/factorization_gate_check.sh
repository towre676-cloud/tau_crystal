#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ts="$(date -u +%Y%m%dT%H%M%SZ)"
out=".tau_ledger/freed/factorization_gate_${ts}.json"
mkdir -p ".tau_ledger/freed"
have_logB="$(ls -1t analysis/freed/logB_receipt_*.json 2>/dev/null | head -n1 || true)"
have_relidx="$(ls -1t analysis/freed/relative_index_*.json 2>/dev/null | head -n1 || true)"
status="pending"; note="awaiting inputs for fuller checks"
[ -n "$have_logB" ] && [ -n "$have_relidx" ] && status="ok" && note="minimal gate satisfied: logB+relative_index present"
printf "{\\n  \\"angle\\": \\"06_factorization_gate\\",\\n  \\"timestamp\\": \\"%s\\",\\n  \\"status\\": \\"%s\\",\\n  \\"have_logB\\": \\"%s\\",\\n  \\"have_relative_index\\": \\"%s\\",\\n  \\"note\\": \\"%s\\"\\n}\\n" "$ts" "$status" "$have_logB" "$have_relidx" "$note" > "$out"
echo "$out"
