#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
AT="analysis/atlas.jsonl"; [ -s "$AT" ] || { echo "[atlas] no atlas; ok (nothing to check)"; exit 0; }
prev_has() { git rev-parse --verify -q HEAD^ >/dev/null 2>&1 && git show HEAD^:"$AT" >/dev/null 2>&1; }
if prev_has; then
  OLD_LINES=$(git show HEAD^:"$AT" | wc -l | tr -d " ")
  NEW_LINES=$(wc -l < "$AT" | tr -d " ")
  [ "$NEW_LINES" -ge "$OLD_LINES" ] || { echo "[atlas] line count decreased ($NEW_LINES < $OLD_LINES)"; exit 10; }
  git diff --unified=0 HEAD^ -- "$AT" | awk '/^-/ && !/^---/ { bad=1 } END{ exit bad?1:0 }' && true || { echo "[atlas] deletions detected"; exit 11; }
fi
awk 'BEGIN{ok=1} /^[[:space:]]*$/ {next} {line=$0; if(line !~ /^\{.*\}$/){print "[atlas] not JSON object:", NR; ok=0} } END{exit ok?0:1}' "$AT" || { echo "[atlas] invalid JSONL object lines"; exit 12; }
tail -n 50 "$AT" | awk -v RS="\n" '/'\"type\"'/{
  if($0 ~ /\"type\":\"SIDECAR_IMPORT\"/ && $0 !~ /^\{"type":"SIDECAR_IMPORT","pack_sha256":"[a-f0-9]{64}","schema":"side-car-v1","ts":"[^\"]+"\}$/){print "[atlas] bad SIDECAR_IMPORT key order or fields"; exit 13}
  if($0 ~ /\"type\":\"REFEREE_CLI\"/ && $0 !~ /^\{"type":"REFEREE_CLI","bin_hash":"[a-f0-9]{64}","ts":"[^\"]+"\}$/){print "[atlas] bad REFEREE_CLI line"; exit 14}
  if($0 ~ /\"type\":\"RANK_STAMP\"/ && $0 !~ /\"zero_hash\":\"[a-f0-9]{64}\",\"rank_hash\":\"[a-f0-9]{64}\"/){print "[atlas] rank stamp missing hashes"; exit 15}
}' >/dev/null 2>&1 || exit $?
echo "[atlas] append-only + grammar OK"
