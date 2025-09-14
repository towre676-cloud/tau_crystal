#!/usr/bin/env bash
# docker_receipt_label.sh — print OCI label "org.opencontainers.image.source.receipt=sha256:<H>"
set -Eeuo pipefail; set +H; umask 022
REC_DIR=".tau_ledger/receipts"; REC=$(ls -1 "$REC_DIR"/*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "${REC:-}" ] || { echo "[ERR] no receipt in $REC_DIR" >&2; exit 2; }
sha(){ if command -v scripts/sha256.sh "$file"
H="$(sha "$REC")"
printf "%s" "org.opencontainers.image.source.receipt=sha256:$H"
