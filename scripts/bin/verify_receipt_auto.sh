#!/usr/bin/env bash
set -euo pipefail; set +H
REC="${1:?receipt}"; C="${2:-}"
if command -v jq >/dev/null 2>&1; then H_IN="$(jq -r ".input_sha256" "$REC")"; H_REQ="$(jq -r ".request_sha256" "$REC")"; else H_IN="$(grep -o "\"input_sha256\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$REC" | sed -E "s/.*:\"([^\"]*)\".*/\\1/")"; H_REQ="$(grep -o "\"request_sha256\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$REC" | sed -E "s/.*:\"([^\"]*)\".*/\\1/")"; fi
echo "receipt.input_sha256  = $H_IN"
echo "receipt.request_sha256= $H_REQ"
[ -n "$C" ] && [ -f "$C" ] && {
  H_UTF=$(scripts/bin/json_sha256.sh "$C");   echo "contract utf8  = $H_UTF"
  H_ASC=$(scripts/bin/json_sha256_ascii.sh "$C"); echo "contract ascii = $H_ASC"
  [ "$H_UTF" = "$H_IN" ]  && echo "[MATCH] input==contract (utf8)"  || true
  [ "$H_ASC" = "$H_IN" ]  && echo "[MATCH] input==contract (ascii)" || true
}
REQ="${3:-}"; [ -n "$REQ" ] && [ -f "$REQ" ] && {
  R_UTF=$(scripts/bin/json_sha256.sh "$REQ");   echo "request utf8  = $R_UTF"
  R_ASC=$(scripts/bin/json_sha256_ascii.sh "$REQ"); echo "request ascii = $R_ASC"
  [ "$R_UTF" = "$H_REQ" ] && echo "[MATCH] request (utf8)"  || true
  [ "$R_ASC" = "$H_REQ" ] && echo "[MATCH] request (ascii)" || true
}
