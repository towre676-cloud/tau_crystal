#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
data="$*"
if command -v sha256sum >/dev/null 2>&1; then
  printf "%s" "$data" | sha256sum | awk "{print \$1\"\t\"ENVIRON[\"ts\"]}"
elif command -v shasum >/dev/null 2>&1; then
  printf "%s" "$data" | shasum -a 256 | awk "{print \$1\"\t\"ENVIRON[\"ts\"]}"
elif command -v openssl >/dev/null 2>&1; then
  printf "%s" "$data" | openssl dgst -sha256 -r | awk "{print \$1\"\t\"ENVIRON[\"ts\"]}"
else
  echo "sha256 tool not found" >&2; exit 1
fi
