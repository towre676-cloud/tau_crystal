#!/usr/bin/env bash
# crash-proof judge_latest: no arrays, no stat, no nullglob, no set -e
set +e +o pipefail; umask 022
LOG="analysis/morpho/judge_latest.log"
mkdir -p "$(dirname "$LOG")"
: > "$LOG"
printf '=== judge_latest %s ===\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$LOG"

# Find newest cert by simple -nt comparisons
latest=""
for f in analysis/morpho/certificates/cert_*.json; do
  # If the glob didn't match, it will be a literal string with '*'
  case "$f" in
    *'*'*) break;;
  esac
  if [ -z "$latest" ] || [ "$f" -nt "$latest" ]; then
    latest="$f"
  fi
done

if [ -z "$latest" ] || [ ! -f "$latest" ]; then
  echo "[fail] no certificates found" | tee -a "$LOG"
  exit 3
fi

echo "[pick] using cert: $latest" >> "$LOG"

# Normalize line endings and ensure judge is executable
sed -i 's/\r$//' scripts/morpho/cert_judge.sh 2>/dev/null || true
chmod +x scripts/morpho/cert_judge.sh 2>/dev/null || true

# Run judge, append all output to the log, and propagate exit code
scripts/morpho/cert_judge.sh "$latest" >> "$LOG" 2>&1
rc=$?
echo "[done] judge exit=$rc" >> "$LOG"
exit $rc
