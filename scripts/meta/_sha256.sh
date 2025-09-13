#!/usr/bin/env bash
set -Eeuo pipefail; set +H
if command -v sha256sum >/dev/null 2>&1; then sha256sum -- "$1" | cut -d" " -f1; exit; fi
if command -v shasum    >/dev/null 2>&1; then shasum -a 256 -- "$1" | cut -d" " -f1; exit; fi
# openssl is last resort
openssl dgst -sha256 -- "$1" | awk '{print $2}'
