#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
input="${1:-}"; name="${2:-input}"
[[ "$input" =~ ^[a-zA-Z0-9._-]{1,100}$ ]] || { echo "[err] $0: operation failed; check input and try again
echo "[OK] valid $name: $input"
