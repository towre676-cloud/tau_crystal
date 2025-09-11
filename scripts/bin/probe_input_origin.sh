#!/usr/bin/env bash
set -euo pipefail; set +H
REC="${1:?receipt}"; REQ="${2:-}"; CONTRACT="${3:-}"
h_in="$(jq -r ".input_sha256" "$REC" 2>/dev/null || grep -o "\"input_sha256\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$REC" | sed -E "s/.*:\"([^\"]*)\".*/\\1/")"
printf "%-24s %s\n" "Receipt input_sha256:" "$h_in"
[ -n "$REQ" ] && [ -f "$REQ" ] && {
  h_req=$(scripts/bin/json_hash.sh "$REQ" || true); printf "%-24s %s\n" "Hash(request):" "$h_req"
  if command -v jq >/dev/null 2>&1; then
    inp="$(jq -e ".input" "$REQ" >/dev/null && echo yes || echo no)";
    if [ "$inp" = yes ]; then
      h_req_inp="$(jq -S -c ".input" "$REQ" | (sha256sum 2>/dev/null || openssl dgst -sha256) | awk "{print \$1}")";
      printf "%-24s %s\n" "Hash(request.input):" "$h_req_inp"
    fi
  fi
}
[ -n "$CONTRACT" ] && [ -f "$CONTRACT" ] && {
  h_c_raw=$(scripts/bin/json_hash.sh "$CONTRACT" || true); printf "%-24s %s\n" "Hash(contract raw):" "$h_c_raw"
  h_c_res=$(scripts/bin/json_hash_resolved.sh "$CONTRACT" || true); printf "%-24s %s\n" "Hash(contract resolved):" "$h_c_res"
}
exit 0
