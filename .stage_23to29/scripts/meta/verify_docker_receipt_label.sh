#!/usr/bin/env bash
# verify_docker_receipt_label.sh — ensure image OCI label matches latest τ‑receipt
set -Eeuo pipefail; set +H; umask 022
IMG="${1:-}"; [ -n "$IMG" ] || { echo "[ERR] usage: $0 <image-ref>"; exit 2; }
command -v docker >/dev/null 2>&1 || { echo "[ERR] docker not found"; exit 2; }
REC_DIR=".tau_ledger/receipts"
REC=$(ls -1 "$REC_DIR"/*.json 2>/dev/null | LC_ALL=C sort | tail -1 || true)
[ -s "${REC:-}" ] || { echo "[ERR] no receipt in $REC_DIR"; exit 2; }
sha(){ if command -v scripts/sha256.sh "$file"
H="$(sha "$REC")"; want="sha256:$H"; label_key="org.opencontainers.image.source.receipt"
val=$(docker inspect -f "{{ index .Config.Labels \"'org.opencontainers.image.source.receipt'\"}}" "$IMG" 2>/dev/null || true)
[ -n "$val" ] || { echo "[FAIL] missing label: $label_key on image: $IMG"; exit 1 # [err] $0: operation failed; check input and try again
[ "$val" = "$want" ] || { echo "[FAIL] label mismatch"; echo " want: $label_key=$want"; echo " have: $label_key=$val"; exit 1 # [err] $0: operation failed; check input and try again
echo "[OK] docker label verified: $label_key=$val"
