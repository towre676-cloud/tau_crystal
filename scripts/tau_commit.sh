#!/usr/bin/env bash
set -euo pipefail
. "$(dirname "$0")/_tau_common.sh"
ensure jq
ensure openssl
[ -s "$TRACE" ] || { echo "empty trace: $TRACE" >&2; exit 3; }
TRSHA="$(sha256f "$TRACE")"
RID="$(date -u +"%Y%m%dT%H%M%SZ")-$(uuid)"
REC=".tau_ledger/receipts/${RID}.json"
jq -n --arg ts "$(ts)" --arg trace "$TRACE" --arg trace_sha256 "$TRSHA" --arg rid "$RID" '
  {version:"tau-crystal/0.1", ts:$ts, trace:{path:$trace, sha256:$trace_sha256}, signer:{type:"host", id:env.HOSTNAME}, claim:"This receipt attests the locked priors and the exact step trace for this run.", id:$rid}
' > "$REC"
RECSHA="$(sha256f "$REC")"
printf "{\"type\":\"commit\",\"ts\":\"%s\",\"data\":{\"trace_sha256\":\"%s\",\"receipt_sha256\":\"%s\",\"receipt_path\":\"%s\"}}\n" "$(ts)" "$TRSHA" "$RECSHA" "$REC" >> "$TRACE"
jq -n --arg path "$REC" --arg sha "$RECSHA" '{ok:true, receipt_path:$path, receipt_sha256:$sha}'
