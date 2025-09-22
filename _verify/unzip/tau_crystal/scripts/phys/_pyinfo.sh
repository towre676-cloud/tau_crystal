#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
exe=""
for c in python3 python py; do command -v "$c" >/dev/null 2>&1 && exe="$c" && break; done
[ -n "$exe" ] || { echo "[err] no python found (tried: python3, python, py)"; exit 7; }
echo "[ok] using: $(command -v "$exe")"
"$exe" -c "import sys,platform; print(f\\"version={sys.version.split()[0]} impl={platform.python_implementation()}\\")"
