#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
mode="${1:-}"; file="${2:-}"
[ -n "$mode" ] && [ -f "${file:-}" ] || { echo "usage: tau_validate.sh <request|response> <file.json>" >&2; exit 2; }
req_keys(){ grep -Eo "\"(tool|input_path|output_path)\"[[:space:]]*:" "$1" | sort | uniq | wc -l; }
has(){ grep -q "\"$2\"[[:space:]]*:" "$1"; }
case "$mode" in
  request)
    [ "$(req_keys "$file")" -ge 3 ] && has "$file" tool && has "$file" input_path && has "$file" output_path || { echo "[invalid request] missing required keys" >&2; exit 3; }
    ;;
  response)
    has "$file" ok || { echo "[invalid response] missing ok" >&2; exit 4; }
    ;;
  *) echo "mode must be request|response" >&2; exit 2;;
esac
echo "[valid] $mode: $file"
