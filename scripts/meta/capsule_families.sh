#!/usr/bin/env bash
set -euo pipefail; umask 022
name="${1:-}"
[ -n "$name" ] || { echo "usage: $0 <capsule-name>"; exit 1; }
dst="analysis/capsules/$name"; mkdir -p "$dst"
add(){ src="$1"; nick="$2"; [ -e "$src" ] || return 0; cp -a "$src" "$dst/$nick"; echo "[CAP] $nick"; }
add ".tau_ledger/discovery/double_zero.json" "double_zero.json"
add ".tau_ledger/discovery/confirm_double_zero_stable.json" "confirm_double_zero_stable.json"
add "analysis/atlas/11a1/ap.tsv" "atlas_11a1_ap.tsv"
add ".tau_ledger/langlands/ap.json" "ledger_ap.json"
add "analysis/geom/proof.dot" "geom_proof.dot"
add "analysis/dynamics/tanh_lineage.json" "tanh_lineage.json"
printf '{"capsule":"%s","created":"%s"}\n' "$name" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" > "$dst/manifest.json"
echo "[CAP] wrote $dst"
