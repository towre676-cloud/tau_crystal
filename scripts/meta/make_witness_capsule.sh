#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
name="${1:-}"
[ -n "$name" ] || { echo "usage: $0 <capsule-name>"; exit 1; }
dst="analysis/capsules/$name"; mkdir -p "$dst"
stamp="$dst/manifest.json"; : > "$stamp"
add(){ src="$1"; nick="$2"; if [ -e "$src" ]; then cp -a "$src" "$dst/"; printf "  {\"file\":\"%s\",\"sha\":\"%s\"},\n" "$nick" "$(sha256sum "$src" | awk "{print \$1}")" >> "$dst/.files"; fi; }
: > "$dst/.files"
add ".tau_ledger/discovery/double_zero.json" "double_zero.json"
add ".tau_ledger/discovery/confirm_double_zero_stable.json" "confirm_double_zero_stable.json"
add "analysis/atlas/11a1/ap.tsv" "atlas_11a1_ap.tsv"
add ".tau_ledger/langlands/ap.json" "ledger_ap.json"
add "analysis/geom/proof.dot" "geom_proof.dot"
add "analysis/dynamics/tanh_lineage.json" "tanh_lineage.json"
printf "{\n  \"capsule\":\"%s\",\n  \"created\":\"%s\",\n  \"files\":[\n" "$name" "$(date -u +"%Y-%m-%dT%H:%M:%SZ")" >> "$stamp"
sed "$ s/,$//" "$dst/.files" >> "$stamp" 2>/dev/null || true
printf "]}\n" >> "$stamp"
rm -f "$dst/.files"; echo "[CAPSULE] $dst"
