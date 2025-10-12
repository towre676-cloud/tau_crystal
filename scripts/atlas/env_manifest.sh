#!/usr/bin/env bash
set +H; set -euo pipefail; umask 022; export LC_ALL=C
out="${1:-.tau_ledger/spec/env.json}"
mkdir -p "$(dirname "$out")"
pyver="$(python3 -V 2>&1 || python -V 2>&1 || echo unknown)"
pyexe="$(command -v python3 || command -v python || echo unknown)"
opensslver="$(openssl version 2>/dev/null || echo unknown)"
uname_s="$(uname -s 2>/dev/null || echo MINGW)"
uname_r="$(uname -r 2>/dev/null || echo unknown)"
fp_mode="IEEE-754, round-to-nearest, ties-to-even"
printf "{\"py_ver\":\"%s\",\"py_path\":\"%s\",\"openssl\":\"%s\",\"os\":\"%s\",\"os_rel\":\"%s\",\"fp\":\"%s\"}\n" "$pyver" "$pyexe" "$opensslver" "$uname_s" "$uname_r" "$fp_mode" > "$out"
if command -v sha256sum >/dev/null 2>&1; then sha256sum "$out" | awk "{print \$1}"; else openssl dgst -sha256 -r "$out" | awk "{print \$1}"; fi
