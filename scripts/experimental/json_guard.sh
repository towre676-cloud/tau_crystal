#!/usr/bin/env bash
set -Eeuo pipefail; set +H
p="$1"; tries="${2:-5}"
[ -f "$p" ] || { echo "[guard] skip missing $p"; exit 0; }
for i in $(seq 1 "$tries"); do
  python scripts/experimental/_json_sanitize.py "$p" || true
  python scripts/experimental/_stamp_provenance.py "$p" || true
  python scripts/experimental/_json_sanitize.py "$p" || true
  python - "$p" <<PY || true
import json,sys; json.load(open(sys.argv[1],encoding="utf-8")); print("[guard-ok]",sys.argv[1])
PY
  if tail -c 1 "$p" | od -An -t x1 | grep -qi "0a"; then
    exit 0
  fi
  sleep 0.2
done
echo "[guard-warn] unstable JSON after retries: $p" >&2
