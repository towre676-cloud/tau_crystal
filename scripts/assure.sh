#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
cd "$root"
echo "[assure] building with Lake…"
lake build
mkdir -p out
manifest="out/manifest.json"
stdout_path="out/fusion.stdout.txt"
if lake exe fusion --help >/dev/null 2>&1; then
  echo "[assure] running fusion…"
  lake exe fusion | tee "$stdout_path" >/dev/null
  producer="fusion"
else
  echo "[assure] fusion not found; writing stub stdout"
  echo "(fusion not present; update scripts/assure.sh when the executable emits a manifest)" > "$stdout_path"
  producer="assure-stub"
fi
git_hash="$(git rev-parse HEAD)"
ts="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
{
  echo "{"
  echo "  \"kind\": \"tau-crystal-receipt\","
  echo "  \"produced_by\": \"${producer}\","
  echo "  \"git\": \"${git_hash}\","
  echo "  \"timestamp\": \"${ts}\","
  echo "  \"stdout_path\": \"${stdout_path}\""
  echo "}"
} > "$manifest"
echo "[assure] wrote $manifest"
