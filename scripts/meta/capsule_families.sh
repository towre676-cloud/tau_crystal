#!/usr/bin/env bash
set -euo pipefail; umask 022
name="${1:-auto-$(date -u +%Y%m%dT%H%M%SZ)}"
dst="analysis/capsules/$name"; mkdir -p "$dst"
cp_if(){ [ -e "$1" ] && cp -a "$1" "$dst/$2" && echo "[CAP] $2" || true; }

cp_if ".tau_ledger/discovery/double_zero.json" "double_zero.json"
cp_if ".tau_ledger/discovery/confirm_double_zero_stable.json" "confirm_double_zero_stable.json"
cp_if "analysis/atlas/11a1/ap.tsv" "atlas_11a1_ap.tsv"
cp_if ".tau_ledger/langlands/ap.json" "ledger_ap.json"
cp_if "analysis/geom/proof.dot" "geom_proof.dot"
cp_if "analysis/dynamics/tanh_lineage.json" "tanh_lineage.json"
printf '{"capsule":"%s","created":"%s"}\n' "$name" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$dst/manifest.json"

bash scripts/capsule/seal_capsule.sh "$dst"
echo "[CAP] wrote $dst"
