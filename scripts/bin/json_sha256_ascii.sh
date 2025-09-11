#!/usr/bin/env bash
set -euo pipefail; set +H
f="${1:?json file}"
canon="$(python3 - "$f" <<PY
import sys,json,pathlib
p=pathlib.Path(sys.argv[1])
with p.open("rb") as fh: obj=json.load(fh)
s=json.dumps(obj,sort_keys=True,separators=(",",":"),ensure_ascii=True)
sys.stdout.write(s)
PY
)"
if command -v sha256sum >/dev/null 2>&1; then printf "%s" "$canon" | sha256sum | awk "{print \$1}"; else printf "%s" "$canon" | openssl dgst -sha256 | awk "{print \$2}"; fi
