#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
ts=$(date -u +%Y%m%d-%H%M%S 2>/dev/null || python - <<PY
import datetime; print(datetime.datetime.utcnow().strftime("%Y%m%d-%H%M%S"))
PY
)
log=".tau_ledger/logs/weekly_${ts}.log"; : > "$log"
say(){ printf "%s\n" "$*" | tee -a "$log" 1>/dev/null; echo "$*"; }
say "[weekly] start ts=$ts commit=$(git rev-parse --short=12 HEAD 2>/dev/null || echo nogit)"
if [ -x scripts/assure/poison_canary.sh ]; then
  say "[weekly] canary: checking timeline continuity…"
  if scripts/assure/poison_canary.sh >> "$log" 2>&1; then
    say "[weekly] canary ok"
  else
    echo "[weekly] ABORT: poison canary failed; see $log" | tee -a "$log"; exit 12
  fi
else
  say "[weekly] canary missing (scripts/assure/poison_canary.sh); skipping gate"
fi
labels=$(awk -F\" '/\"label\":/{for(i=1;i<=NF;i++) if($i=="label") print $(i+2)}' analysis/atlas/atlas_hecke.jsonl 2>/dev/null | sort -u)
[ -n "$labels" ] || labels="11a1 37a1"
say "[weekly] labels: $labels"
for L in $labels; do
  if [ -x scripts/assure/adversarial_recount.sh ]; then
    say "[weekly] adversarial recount: $L"
    scripts/assure/adversarial_recount.sh "$L" >> "$log" 2>&1 || say "[weekly] adversarial recount failed for $L (non-fatal)"
  else
    say "[weekly] adversarial script missing; skipping $L"
  fi
  main="analysis/atlas/$L/ap.tsv"; mir="analysis/atlas/$L/ap_mirror.tsv"
  if [ -x scripts/assure/mirror_world_compare.sh ] && [ -s "$mir" ] && [ -s "$main" ]; then
    say "[weekly] mirror compare: $L"
    scripts/assure/mirror_world_compare.sh "$L" "$main" "$mir" >> "$log" 2>&1 || say "[weekly] mirror compare failed for $L (non-fatal)"
  else
    [ -s "$mir" ] || say "[weekly] no mirror payload for $L; skipping mirror gate"
  fi
done
git add -A analysis/atlas.jsonl .tau_ledger POISON 2>/dev/null || true
if git diff --cached --quiet; then
  say "[weekly] no changes to commit"
else
  msg="assure: weekly cadence receipts (canary+lottery+mirror) $ts"
  if git commit -m "$msg" >> "$log" 2>&1; then
    say "[weekly] committed: $(git rev-parse --short=12 HEAD)"
  else
    say "[weekly] commit failed (non-fatal); see $log"
  fi
fi
say "[weekly] done: log=$log"
