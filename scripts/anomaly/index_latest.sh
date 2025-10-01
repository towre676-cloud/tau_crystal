#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
. "$(dirname "$0")/_hash.sh"
LATEST_DIR="analysis/_runs/latest_anomaly"
d="$(ls -d analysis/_runs/anomaly_* 2>/dev/null | sort | tail -n 1 || true)"
[ -n "${d:-}" ] || { echo "[err] no anomaly_* runs"; exit 2; }
mkdir -p "$LATEST_DIR"
cp -f "$d/dK_triplet.json" "$LATEST_DIR/dK_triplet.json"
B="bulk_logdet.json"; E="eta_boundary.json"; R="logB_receipt.json"
bh="$(hash_file "$B")"; eh="$(hash_file "$E")"; rh="$(hash_file "$R")"
: > "$LATEST_DIR/manifest.txt"
echo "artifact_dir: $d"                                >> "$LATEST_DIR/manifest.txt"
echo "artifact:     $LATEST_DIR/dK_triplet.json"       >> "$LATEST_DIR/manifest.txt"
echo "bulk:         $B (# $bh)"                        >> "$LATEST_DIR/manifest.txt"
echo "eta:          $E (# $eh)"                        >> "$LATEST_DIR/manifest.txt"
echo "relative:     $R (# $rh)"                        >> "$LATEST_DIR/manifest.txt"
echo "[ok] indexed → $LATEST_DIR/dK_triplet.json"
