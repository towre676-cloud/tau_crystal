#!/usr/bin/env bash
set -euo pipefail
# b3sum shim for Windows dev shells
if ! command -v b3sum >/dev/null 2>&1; then b3sum(){ sha256sum "$@"; }; export -f b3sum 2>/dev/null || true; fi

LEAN_VER="$( (lean --version 2>/dev/null || echo unknown) | head -n1 )"
LAKE_VER="$( (lake --version 2>/dev/null || echo unknown) | head -n1 )"
MANI="$(test -f lake-manifest.json && cat lake-manifest.json || echo '{}')"
MATH_SHA="$(printf '%s' "$MANI" | jq -r '.packages[]? | select(.name=="mathlib") | (.rev // .git // "unknown")' 2>/dev/null || echo unknown)"
GRAMMAR_HASH="$(test -s .tau_ledger/verify_grammar.lean && b3sum .tau_ledger/verify_grammar.lean | awk '{print $1}' || echo none)"

printf '%s\n' "$LEAN_VER" "$LAKE_VER" "$MATH_SHA" "$GRAMMAR_HASH" | b3sum | awk '{print $1}'
