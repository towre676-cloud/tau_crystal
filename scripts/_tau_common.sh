#!/usr/bin/env bash
set -euo pipefail
ts(){ date -u +%Y-%m-%dT%H:%M:%SZ; }
sha256f(){
  if command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | awk "{print \$1}";
  elif command -v certutil >/dev/null 2>&1; then certutil -hashfile "$1" SHA256 | awk "NR==2{gsub(/ /,\"\");print tolower(\$0)}";
  else echo "no sha256 tool" >&2; exit 127; fi
}
uuid(){ { command -v uuidgen >/dev/null && uuidgen; } || openssl rand -hex 16; }
ensure(){ command -v "$1" >/dev/null || { echo "missing: $1" >&2; exit 127; }; }
mkdir -p .tau_ledger
TRACE=".tau_ledger/trace.ndjson"
