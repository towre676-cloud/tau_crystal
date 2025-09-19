#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
cd "$(git rev-parse --show-toplevel 2>/dev/null || pwd)" || exit 1

echo "[postflight] branch=$(git rev-parse --abbrev-ref HEAD) head=$(git rev-parse --short HEAD)"

scan="analysis/bash_theta_scan.tsv"
morse="analysis/morse_crit.tsv"

# counts
if [ -f "$scan" ]; then rows="$(wc -l < "$scan" 2>/dev/null || echo 0)"; else rows=0; fi
echo "[postflight] scan rows (incl header): $rows"
if [ -f "$morse" ]; then
  mins="$(grep -c $'\tminimum\t' "$morse" 2>/dev/null || echo 0)"
  [ "$mins" -eq 0 ] && mins="$(grep -c $'\tmin$' "$morse" 2>/dev/null || echo 0)"
else
  mins=0
fi
echo "[postflight] minima: $mins"

# ensure exec bits (no arrays)
fix_exec() { f="$1"; [ -f "$f" ] && [ ! -x "$f" ] && chmod +x "$f"; printf "[exec] %-40s %s\n" "$f" "$([ -x "$f" ] && echo OK || echo MISSING)"; }
fix_exec scripts/langlands/run_phase_next.sh
fix_exec scripts/langlands/morse_analysis.sh
fix_exec scripts/langlands/morse2d_pure.sh
fix_exec scripts/langlands/theta_scan_proxy2.sh
fix_exec scripts/langlands/basins_map.sh
fix_exec scripts/langlands/atlas_line.sh
fix_exec scripts/langlands/live_ticker.sh
fix_exec scripts/langlands/update_ledger.sh

# monograph index
mono_dir="docs/monographs"; mkdir -p "$mono_dir"
origin="$(git remote get-url origin 2>/dev/null || echo "")"
case "$origin" in
  https://github.com/*) base="$origin" ;;
  git@github.com:*)     base="https://github.com/${origin#git@github.com:}" ;;
  *)                    base="$origin" ;;
esac
base="${base%.git}"
index="$mono_dir/_index.md"
{
  echo "# τ-Crystal Langlands Monographs"
  echo
  printf "_Auto-generated: %s_\n\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  for f in $(ls -1 "$mono_dir"/*.md 2>/dev/null | sort); do
    rel="${f#./}"
    url="$base/blob/main/$rel"
    title="$(sed -n 's/^# \{0,1\}//p;q' "$f" 2>/dev/null)"
    [ -n "$title" ] || title="$(basename "$f")"
    echo "- [$title]($url)"
  done
} > "$index"
echo "[index] wrote $index"

# ledger anchor
[ -x scripts/langlands/update_ledger.sh ] && bash scripts/langlands/update_ledger.sh

# commit + push
git add -A
git commit -m "postflight: monograph index + exec bits + ledger $(date -u +%Y-%m-%dT%H:%M:%SZ)" || true
br="$(git rev-parse --abbrev-ref HEAD)"
git pull --rebase origin "$br" || true
git push -u origin "$br"

echo
echo "[links]"
echo "  monograph index: $base/blob/main/$index"
echo "  latest ledger  : $base/blob/main/.tau_ledger/langlands/phase_next_latest.sha"
