#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
RUN_ID="${RUN_ID:-$(date -u +%Y%m%d-%H%M%S)}"; export RUN_ID
series="${1:-.tau_ledger/signals/observable.tsv}"
[ -s "$series" ] || { echo "[err] missing series: $series" >&2; exit 2; }
cal="$(scripts/tau_sweep.sh "$series")"
scripts/tau_fuse.sh >/dev/null 2>&1 || true
rec=".tau_ledger/calibration/${RUN_ID}.receipt.json"; : > "$rec"
printf "%s\n" "{" >> "$rec"
printf "%s\n" "  \"schema\":\"taucrystal/receipt/v1\"," >> "$rec"
printf "%s\n" "  \"tau_class\":\"ensemble\"," >> "$rec"
printf "%s\n" "  \"calibration_ref\":\"${cal}\"," >> "$rec"
printf "%s\n" "  \"signals\":{\"ensemble\":\".tau_ledger/tau/ensemble.tsv\"}," >> "$rec"
printf "%s\n" "  \"provenance\":{\"run_id\":\"$RUN_ID\",\"ts\":\"$(date -u +%Y-%m-%dT%H:%M:%SZ)\",\"host\":\"$(hostname)\"}" >> "$rec"
printf "%s\n" "}" >> "$rec"
echo "$rec"
