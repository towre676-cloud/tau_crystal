#!/usr/bin/env bash
set -euo pipefail; set +H
REC="${1:?path to receipt.json}"
OVERRIDE="${2:-}"
if command -v jq >/dev/null 2>&1; then
  IN_SHA="$(jq -r ".input_sha256" "$REC")"
  REQ_SHA="$(jq -r ".request_sha256" "$REC")"
  CONTRACT="${OVERRIDE:-$(jq -r ".contract_path // empty" "$REC")}"
else
  IN_SHA="$(grep -o "\"input_sha256\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$REC" | sed -E "s/.*:\"([^\"]*)\".*/\\1/")"
  REQ_SHA="$(grep -o "\"request_sha256\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$REC" | sed -E "s/.*:\"([^\"]*)\".*/\\1/")"
  CONTRACT="$OVERRIDE"
fi
[ -n "${CONTRACT:-}" ] || { echo "[err] contract_path missing; pass explicit path as 2nd arg"; exit 1; }
H_ASC="$(scripts/bin/json_sha256_ascii.sh "$CONTRACT")"
H_UTF="$(scripts/bin/json_sha256.sh "$CONTRACT")"
echo "receipt input_sha256:   $IN_SHA"
echo "contract ascii sha256:  $H_ASC"
echo "contract utf8  sha256:  $H_UTF"
if [ "$H_ASC" = "$IN_SHA" ]; then
  echo "[OK] match (ascii canonical)"
elif [ "$H_UTF" = "$IN_SHA" ]; then
  echo "[OK] match (utf8 canonical)"
else
  echo "[FAIL] no match (ascii/utf8)"; exit 2
fi
