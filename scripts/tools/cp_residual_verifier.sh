#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
IN="${1:-}"; OUT="${2:-}"
[ -n "${IN}" ] && [ -n "${OUT}" ] && [ -f "${IN}" ] || { printf '{"ok":false,"error":"usage: cp_residual_verifier.sh <in.json> <out.json>"}\n' > "${OUT:-/dev/stdout}"; exit 2; }
command -v python3 >/dev/null 2>&1 || { printf '{"ok":false,"error":"python3_not_found"}\n' > "${OUT}"; exit 0; }
python3 scripts/tools/cp_residual_verifier.py "$IN" > "$OUT" 2>/dev/null || printf '{"ok":false,"error":"python_failed"}\n' > "$OUT"
