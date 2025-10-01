#!/usr/bin/env bash
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
ts="$(date -u +%Y%m%dT%H%M%SZ)"
out="analysis/freed/aps_split_${ts}.json"
bulk="$(ls -1t analysis/**/bulk_logdet_*.json .tau_ledger/**/bulk_logdet_*.json 2>/dev/null | head -n1 || true)"
bdry="$(ls -1t analysis/**/eta_boundary_*.json .tau_ledger/**/eta_boundary_*.json 2>/dev/null | head -n1 || true)"
logB="$(ls -1t analysis/**/logB_receipt_*.json .tau_ledger/**/logB_receipt_*.json 2>/dev/null | head -n1 || true)"
[ -n "$bulk" ] && [ -n "$bdry" ] && [ -n "$logB" ] || { echo "[aps] missing inputs"; exit 0; }
# naive compare scaffold (replace with your spectral boundary math)
vb="$(python - <<PY\nimport json,sys;print(json.load(open(sys.argv[1],"r",encoding="utf-8")).get("value") or 0.0)\nPY "$bulk")"
ve="$(python - <<PY\nimport json,sys;print(json.load(open(sys.argv[1],"r",encoding="utf-8")).get("eta") or 0.0)\nPY "$bdry")"
vl="$(python - <<PY\nimport json,sys;print(json.load(open(sys.argv[1],"r",encoding="utf-8")).get("logB") or 0.0)\nPY "$logB")"
resid=$(python - <<PY\nimport sys; vb=float(sys.argv[1]); ve=float(sys.argv[2]); vl=float(sys.argv[3]); print(vb+ve-vl)\nPY "$vb" "$ve" "$vl")
printf "{\\n  \\"angle\\": \\"04_aps_split\\",\\n  \\"timestamp\\": \\"%s\\",\\n  \\"status\\": \\"ok\\",\\n  \\"residual\\": %s,\\n  \\"inputs\\": { \\"bulk_logdet\\": \\"%s\\", \\"eta_boundary\\": \\"%s\\", \\"logB_receipt\\": \\"%s\\" }\\n}\\n" "$ts" "$resid" "$bulk" "$bdry" "$logB" > "$out"
echo "$out"
