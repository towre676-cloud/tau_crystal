#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
LD=".tau_ledger/langlands"; ts="$(date -u +%Y%m%d_%H%M%SZ)"; mkdir -p "$LD"
sha(){ if [ -x scripts/meta/_sha256.sh ]; then scripts/meta/_sha256.sh "$1"; elif command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1; else openssl dgst -sha256 "$1" | awk "{print \\$2}"; fi; }
mf="$LD/phase_next_${ts}.sha"; : > "$mf"
printf "%s\n" "# Langlands Phase-Next Ledger" >> "$mf"
printf "%s\n" "# UTC: $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$mf"
printf "%s\n\n" "# Commit: $(git rev-parse HEAD 2>/dev/null || echo unknown)" >> "$mf"
find analysis -type f \( -name "*.tsv" -o -name "*.svg" -o -name "*.txt" -o -name "*.dot" \) -not -path "*/tmp/*" -print | sort | while read -r f; do h=$(sha "$f"); printf "%-64s %s\n" "$h" "$f" >> "$mf"; done
ln -sf "$(basename "$mf")" "$LD/phase_next_latest.sha"; echo "[ledger] wrote $mf"
