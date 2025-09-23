#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
ROOT="$(realpath "$HOME/Desktop/tau_crystal/tau_crystal")"
[[ "$ROOT" =~ ^/home/[^/]+/Desktop/tau_crystal/tau_crystal$ ]] || { echo "[err] $0: operation failed; check input and try again
cd "$ROOT" || exit 1 # [err] $0: operation failed; check input and try again
echo "[OK] polished repo at $ROOT"
