#!/usr/bin/env bash
set -euo pipefail
INFILE="${1:-tmp/P2P.ndjson}"
mkdir -p manifests
[ -s "$INFILE" ] || { echo "{}" > "$INFILE"; }
hash=$(printf "%s" "$INFILE" | sha1sum 2>/dev/null | awk "{print \$1}")
out="manifests/${hash}.json"
printf "%s\n" "{" > "$out"
printf "%s\n" "  \"kind\": \"tau-crystal-receipt\"," >> "$out"
printf "%s\n" "  \"version\": \"1.2.0\"," >> "$out"
printf "%s\n" "  \"process\": {\"id\":\"PO-demo\",\"domain\":\"P2P\",\"segment\":\"PO.created\",\"prev_manifest\":\"\"}," >> "$out"
printf "%s\n" "  \"tau\": {\"t\":[0.0],\"clock\":\"Chebyshev-decay\",\"params\":{\"tau_min\":0.06,\"slope\":0.3}}," >> "$out"
printf "%s\n" "  \"residue\": {\"R_norm\":0.0,\"D_norm\":0.0,\"kappa\":0.1591549431,\"qcro\":[]}," >> "$out"
printf "%s\n" "  \"witness\": {\"events_sha\":\"sha256:placeholder\",\"pivot_transcript\":\"sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\",\"rank_signature\":{\"p\":2147482951,\"rank\":6}}," >> "$out"
printf "%s\n" "  \"sustainability\": {}," >> "$out"
printf "%s\n" "  \"attest\": {\"merkle_root\":\"sha256:placeholder\",\"signed_by\":\"\",\"timestamp\":\"$(date -u +%Y-%m-%dT%H:%M:%SZ)\"}" >> "$out"
printf "%s\n" "}" >> "$out"
echo "[rebuild] wrote $out"
