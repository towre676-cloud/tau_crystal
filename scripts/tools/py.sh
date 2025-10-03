#!/usr/bin/env bash
set -e; set +H
if command -v python3 >/dev/null 2>&1; then exec python3 "$@"; fi
if command -v py >/dev/null 2>&1; then exec py -3 "$@"; fi
if command -v python >/dev/null 2>&1; then exec python "$@"; fi
echo "[err] python interpreter not found"; exit 127
