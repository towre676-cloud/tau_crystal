#!/usr/bin/env bash
set -euo pipefail
repo="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$repo"
mkdir -p .tau_ledger

stamp="$(date -u +%Y%m%dT%H%M%SZ)"
head="$(git rev-parse HEAD 2>/dev/null || echo WORKTREE)"
short="${head:0:12}"

# Ensure fresh audit
scripts/boundary_audit.sh >/dev/null

# small helpers
sha() { [ -f "$1" ] && sha256sum "$1" | awk '{print $1}' || echo ""; }
first() { command -v "$1" >/dev/null 2>&1 && "$@" | head -n1 || echo ""; }

lean_toolchain="$(tr -d '\r' < lean-toolchain 2>/dev/null || echo '')"
lake_manifest_sha="$(sha lake-manifest.json)"
lakefile_sha="$(sha lakefile.lean)"
wh_ax_sha="$(sha boundary/WHITELIST.ax)"
wh_op_sha="$(sha boundary/WHITELIST.opaque)"
wh_un_sha="$(sha boundary/WHITELIST.unsafe)"
assum_tsv_sha="$(sha .tau_ledger/assumptions.tsv)"

uname_s="$(uname -a 2>/dev/null || echo "")"
lean_v="$(first lean --version)"
lake_v="$(first lake --version)"
clang_v="$(first clang --version)"
llvm_v="$(first llvm-config --version)"

out=".tau_ledger/census-$stamp.ndjson"
: > "$out"

emit() { printf '%s\n' "$1" >> "$out"; }

emit "{\"stamp\":\"$stamp\",\"commit\":\"$head\",\"short\":\"$short\"}"
emit "{\"lean_toolchain\":\"$lean_toolchain\"}"
emit "{\"lake_manifest_sha\":\"$lake_manifest_sha\",\"lakefile_sha\":\"$lakefile_sha\"}"
emit "{\"whitelist_sha\":{\"axiom\":\"$wh_ax_sha\",\"opaque\":\"$wh_op_sha\",\"unsafe\":\"$wh_un_sha\"}}"
emit "{\"assumptions_tsv_sha\":\"$assum_tsv_sha\"}"
emit "{\"env\":{\"uname\":\"$uname_s\",\"lean\":\"$lean_v\",\"lake\":\"$lake_v\",\"clang\":\"$clang_v\",\"llvm\":\"$llvm_v\"}}"

cp "$out" .tau_ledger/census.ndjson
echo "$out"
