#!/usr/bin/env bash
set -Eeuo pipefail; set +H
if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}"; exit 0; fi
if command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | awk "{print \$1}"; exit 0; fi
openssl dgst -sha256 "$1" | awk "{print \$2}"
