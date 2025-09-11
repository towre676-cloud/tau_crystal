#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022

# Usage: scripts/lake_with_receipts.sh [build-args...]
# Wraps `lake build` with cryptographic receipts:
# - Hashes toolchain, mathlib commit (if available), Lake manifests, source tree
# - Runs lake build
# - Hashes outputs (.olean by default) and writes a chained JSON receipt
# - Ledger at .tau_ledger/receipts.jsonl with prev_sha256 chaining

sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum | awk "{print \$1}"; else openssl dgst -sha256 | awk "{print \$2}"; fi; }
jqesc(){ awk 'BEGIN{RS="";ORS=""}{gsub(/\\/,"\\\\");gsub(/"/,"\\\"");gsub(/\r/,"");gsub(/\t/,"\\t");gsub(/\n/,"\\n");printf "%s",$0}'; }

ROOT="$(pwd)"
LEDGER=".tau_ledger/receipts.jsonl"
LAST=".tau_ledger/last.sha256"
mkdir -p "$(dirname "$LEDGER")"

# 1) Gather deterministic inputs
TOOLCHAIN="${LEAN_TOOLCHAIN:-$(elan show 2>/dev/null | awk '/default toolchain/ {print $3;exit}')}"
LAKE_VERSION="$(lake --version 2>/dev/null | tr -d "\r")"
MATHLIB_COMMIT="${MATHLIB_COMMIT:-}"  # optional: export if known
MANIFEST_FILES=()
[ -f lakefile.lean ] && MANIFEST_FILES+=("lakefile.lean")
[ -f lake-manifest.json ] && MANIFEST_FILES+=("lake-manifest.json")
[ -f lean-toolchain ] && MANIFEST_FILES+=("lean-toolchain")

src_list=$(mktemp); trap 'rm -f "$src_list"' EXIT
find . -type f \( -name "*.lean" -o -name "lakefile.lean" -o -name "lake-manifest.json" -o -name "lean-toolchain" \) -print0 | sort -z | tr -d "\000" > "$src_list"
inputs_sha=$( ( printf "%s\n" "$TOOLCHAIN"; printf "%s\n" "$LAKE_VERSION"; printf "%s\n" "$MATHLIB_COMMIT"; while IFS= read -r p; do [ -f "$p" ] && cat -- "$p"; done < "$src_list" ) | sha )

# 2) Capture pre-build artifact state (so receipts reflect deltas)
pre_artifacts_sha=$( ( find . -type f -name "*.olean" -print0 | sort -z | xargs -0 cat -- 2>/dev/null || true ) | sha || true )

# 3) Run lake build with user args
build_cmd=(lake build "$@")
start_ts=$(date -u +%FT%TZ)
build_out=$(mktemp); build_err=$(mktemp); trap 'rm -f "$build_out" "$build_err"' EXIT
set +e; "${build_cmd[@]}" >"$build_out" 2>"$build_err"; rc=$?; set -e
end_ts=$(date -u +%FT%TZ)

# 4) Hash post-build artifacts
post_artifacts_sha=$( ( find . -type f -name "*.olean" -print0 | sort -z | xargs -0 cat -- 2>/dev/null || true ) | sha || true )

# 5) Build a chained JSON receipt
prev=""; [ -f "$LAST" ] && prev="$(cat "$LAST" 2>/dev/null || true)"
cmd_json=$(printf "%s" "${build_cmd[*]}" | jqesc)
out_json=$(cat "$build_out" | jqesc)
err_json=$(cat "$build_err" | jqesc)
receipt=$(mktemp)
printf "{"                                 >  "$receipt"
printf "\"tool\":\"lake\",">> "$receipt"
printf "\"args\":\"%s\"," "$cmd_json"   >> "$receipt"
printf "\"start\":\"%s\"," "$start_ts"  >> "$receipt"
printf "\"end\":\"%s\","   "$end_ts"    >> "$receipt"
printf "\"exit\":%s,"      "$rc"        >> "$receipt"
printf "\"toolchain\":\"%s\"," "$(printf "%s" "$TOOLCHAIN" | jqesc)" >> "$receipt"
printf "\"lake_version\":\"%s\"," "$(printf "%s" "$LAKE_VERSION" | jqesc)" >> "$receipt"
printf "\"mathlib_commit\":\"%s\"," "$(printf "%s" "$MATHLIB_COMMIT" | jqesc)" >> "$receipt"
printf "\"inputs_sha256\":\"%s\"," "$inputs_sha" >> "$receipt"
printf "\"pre_artifacts_sha256\":\"%s\"," "$pre_artifacts_sha" >> "$receipt"
printf "\"post_artifacts_sha256\":\"%s\"," "$post_artifacts_sha" >> "$receipt"
printf "\"stdout\":\"%s\"," "$out_json" >> "$receipt"
printf "\"stderr\":\"%s\""  "$err_json" >> "$receipt"
printf "}\n"                          >> "$receipt"
this_sha=$(cat "$receipt" | sha)
printf "%s\n" "$this_sha" > "$LAST"
printf "%s\n" "$(cat "$receipt" | sed -e "s/}$/,\"prev_sha256\":\"$prev\"}/")" >> "$LEDGER"

# Echo a one-line summary for humans/CI
echo "[lake-with-receipts] exit=$rc inputs=$inputs_sha artifacts=$post_artifacts_sha receipt=$this_sha"
exit "$rc"
