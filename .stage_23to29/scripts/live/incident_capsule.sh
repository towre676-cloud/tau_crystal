#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -e
TS=$(date -u +%Y%m%dT%H%M%SZ)
ID="incident_${TS}"
ROOT="analysis/capsules"
OUT="${ROOT}/${ID}"
mkdir -p "$OUT"

# Snapshot artifacts (best-effort copies)
cp -f .tau_ledger/hysteresis/latest_barcode.json "$OUT/barcode.json" 2>/dev/null || true
cp -f .tau_ledger/runtime/current_entropy.json "$OUT/entropy.json" 2>/dev/null || true
cp -f .tau_ledger/runtime/virtualalloc_maps.tsv "$OUT/virtualalloc_maps.tsv" 2>/dev/null || true
cp -f .tau_ledger/invariants/latest.json "$OUT/invariants.json" 2>/dev/null || true
cp -f .tau_ledger/decisions/*.json "$OUT/" 2>/dev/null || true

# Create archive OUTSIDE the folder to avoid "file changed as we read it"
ARCH="${ROOT}/${ID}.tar.gz"
tar -C "$OUT" -czf "$ARCH" .

# Hash and ledger entry
sha256sum "$ARCH" | awk '{print $1}' > "${ARCH}.sha256"
printf "%s\t%s\t%s\n" "$TS" "$ID" "$(cat "${ARCH}.sha256")" >> .tau_ledger/incidents.log
echo "[INCIDENT] sealed $ARCH"
