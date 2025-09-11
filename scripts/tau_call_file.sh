#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
file="${1:-}"; [ -n "$file" ] && [ -f "$file" ] || { echo "[err] usage: tau_call_file.sh <request.json>" >&2; exit 2; }
cat "$file" | bash scripts/tau_pipe.sh
