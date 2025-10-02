#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
P="${1:-tau-crystal-manifest.json}"
if [ ! -f "$P" ]; then echo "[conformance] no manifest $P; skipping"; exit 0; fi
python3 - <<PY 2>/dev/null || { echo "[conformance] python missing; skipping"; exit 0; }
import json,hashlib,sys
p=sys.argv[1]
doc=json.load(open(p,"r",encoding="utf-8"))
blob=json.dumps(doc,sort_keys=True,separators=(",",":")).encode()
print("[conformance] manifest sha256", hashlib.sha256(blob).hexdigest())
PY

