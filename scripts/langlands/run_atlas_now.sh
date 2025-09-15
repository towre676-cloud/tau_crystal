#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022

rowcount(){ f="$1"; if [ -f "$f" ]; then n="$(wc -l < "$f" 2>/dev/null)" || n=""; if [ -z "$n" ]; then c=0; while IFS= read -r _; do c=$((c+1)); done < "$f"; echo "$c"; else echo "$n"; fi; else echo 0; fi; }

# 0) seed witnesses (idempotent)
bash scripts/langlands/seed_witness_envs.sh

# 1) build two-hill Δ surface (atomic)
S_PAD=${S_PAD:-50000} T_PAD=${T_PAD:-50000} S_STEP=${S_STEP:-2000} T_STEP=${T_STEP:-2000} \
bash scripts/langlands/theta_scan_proxy2.sh

# 2) recompute minima + plots
bash scripts/langlands/morse2d_pure.sh analysis/bash_theta_scan.tsv
bash scripts/langlands/basins_map.sh   || true
bash scripts/langlands/atlas_line.sh   || true

# 3) gather stats (pure bash)
ROWS=0
if [ -s analysis/bash_theta_scan.tsv ]; then
  R="$(rowcount analysis/bash_theta_scan.tsv)"
  ROWS=$(( R>0 ? R-1 : 0 ))
fi

MINS=0
if [ -s analysis/morse_crit.tsv ]; then
  first=1
  while IFS=$'\t' read -r s t typ _rest; do
    if [ "$first" = 1 ]; then first=0; case "$s" in ''|*[!0-9-]* ) continue;; esac; fi
    case "$typ" in min*|Min*|MIN*) MINS=$((MINS+1));; esac
  done < analysis/morse_crit.tsv
fi

MIN=""; BS=""; BT=""
if [ -s analysis/bash_theta_scan.tsv ]; then
  first=1
  while IFS=$'\t' read -r s t d _rest; do
    if [ "$first" = 1 ]; then first=0; case "$s" in ''|*[!0-9-]* ) continue;; esac; fi
    case "$d" in ''|*[!0-9-]* ) continue;; esac
    if [ -z "$MIN" ] || [ "$d" -lt "$MIN" ]; then MIN="$d"; BS="$s"; BT="$t"; fi
  done < analysis/bash_theta_scan.tsv
fi

# 4) write a status stamp
mkdir -p analysis
{
  printf "utc=%s\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf "rows=%s\n" "$ROWS"
  printf "minima=%s\n" "$MINS"
  printf "best_delta=%s\n" "${MIN:-NA}"
  printf "best_S=%s\n" "${BS:-NA}"
  printf "best_T=%s\n" "${BT:-NA}"
} > analysis/atlas_status.txt

# 5) ledger snapshot (best-effort)
bash scripts/langlands/update_ledger.sh || true

# 6) commit and push
git add analysis/ .tau_ledger/langlands/ scripts/langlands/*.sh 2>/dev/null || true
git commit -m "atlas(run): rows=${ROWS} minima=${MINS} best=Δ=${MIN:-NA}@S=${BS:-NA},T=${BT:-NA}" || true
git push -u origin "$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main)" || true

# 7) echo summary
printf "[atlas] rows=%s minima=%s best=Δ=%s @ S=%s T=%s\n" "$ROWS" "$MINS" "${MIN:-NA}" "${BS:-NA}" "${BT:-NA}"
