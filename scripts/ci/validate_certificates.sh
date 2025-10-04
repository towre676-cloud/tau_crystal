#!/usr/bin/env bash
set -euo pipefail; set +H; export LC_ALL=C LANG=C
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$root" || exit 1
ok=0; fail=0
for f in certificates/examples/*.json; do
  case "$f" in
    *descent* ) schema=schemas/descent.schema.json;;
    *cone*    ) schema=schemas/cone.schema.json;;
    *reflection* ) schema=schemas/reflection.schema.json;;
    * ) echo "[skip] $f"; continue;;
  esac
  if jq -e . < "$schema" >/dev/null 2>&1 && jq -e . < "$f" >/dev/null 2>&1; then
    echo "[ok] JSON well-formed: $f"
    ok=$((ok+1))
  else
    echo "[fail] JSON malformed: $f"
    fail=$((fail+1))
  fi
done
echo "[summary] ok=$ok fail=$fail"
exit $([ "$fail" -eq 0 ] && echo 0 || echo 1)
