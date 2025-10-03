#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
if command -v sha256sum >/dev/null 2>&1; then sha256sum "$@"; else openssl dgst -sha256 "$@"; fi
