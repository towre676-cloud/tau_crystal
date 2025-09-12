#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
cd "${1:-$PWD}" || { echo "[err] bad root"; exit 1; }
pass(){ printf "[PASS] %s\n" "$1"; }
miss(){ printf "[MISS] %s\n" "$1"; }
[ -x scripts/tau_verify.sh ] && pass "ci guard script present (scripts/tau_verify.sh)" || miss "ci guard script missing (scripts/tau_verify.sh)"
if grep -RIlq "tau_verify.sh" .github/workflows 2>/dev/null; then pass "ci guard referenced in workflows"; else miss "ci guard not referenced in workflows"; fi
if grep -RIlq '\"tau_class\"": ' . .tau_ledger receipts docs 2>/dev/null; then pass "receipts expose tau_class"; else miss "receipts lack tau_class"; fi
if grep -RIlq '\"provenance\"": ' . .tau_ledger receipts docs 2>/dev/null; then pass "receipts expose provenance"; else miss "receipts lack provenance"; fi
if grep -RIlq '\"signals\"": ' . .tau_ledger receipts docs 2>/dev/null; then pass "receipts expose signals"; else miss "receipts lack signals"; fi
if ls scripts/*sweep* 1>/dev/null 2>&1 || grep -RIlq -E "(K[_=: -]|--degree|--K)" scripts 2>/dev/null && grep -RIlq -Ei "(omega|damp)" scripts 2>/dev/null; then pass "K/ω sweep present"; else miss "K/ω sweep not detected"; fi
if grep -RIlq -Ei "(isotonic|PAV|pool[- ]adjacent[- ]violators)" scripts 2>/dev/null; then pass "ensemble τ / isotonic fuse present"; else miss "ensemble τ / isotonic fuse not detected"; fi
if ls scripts/*tau*adapter* 1>/dev/null 2>&1 || grep -RIlq -Ei "(adapter.*sweep|sweep.*emit|emit.*receipt)" scripts 2>/dev/null; then pass "adapter wrapper present"; else miss "adapter wrapper not detected"; fi
if grep -RIlq -Ei "(spec_guard|receipt.*validate|jq.*schema|python.*schema)" .github/workflows scripts 2>/dev/null; then pass "schema/spec guard for receipts detected"; else miss "schema/spec guard for receipts not detected"; fi
