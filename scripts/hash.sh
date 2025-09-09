#!/usr/bin/env bash
set -euo pipefail
f="${1:?usage: hash.sh <file>}"
if command -v b3sum >/dev/null 2>&1; then
  b3sum "$f" | awk '{print $1" blake3"}'
elif command -v python3 >/dev/null 2>&1 && python3 - <<'PY' >/dev/null 2>&1
import sys, importlib.util
sys.exit(0 if importlib.util.find_spec("blake3") else 1)
PY
then
  python3 - <<PY
from blake3 import blake3
import sys, pathlib
p = pathlib.Path(sys.argv[1]).read_bytes()
print(blake3(p).hexdigest(), "blake3")
PY
  "$f"
else
  sha256sum "$f" | awk '{print $1" sha256"}'
fi
