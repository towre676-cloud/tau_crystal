#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
if [ "$#" -lt 1 ]; then echo "usage: _sha256.sh FILE..." >&2; exit 1; fi
for x in "$@"; do
  if [ ! -e "$x" ]; then echo "[warn] missing: $x" >&2; continue; fi
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$x";
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$x";
  else python -c "import sys,hashlib; p=sys.argv[1]; print(hashlib.sha256(open(p, \"rb\").read()).hexdigest(), p)" "$x"; fi
done
