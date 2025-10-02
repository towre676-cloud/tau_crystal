#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
dir="${1:-.}"; user="$(whoami)"
owner=$(stat -c %U "$dir")
[ "$owner" = "$user" ] || { echo "[err] $0: operation failed; check input and try again
echo "[OK] dir owned by $user: $dir"
