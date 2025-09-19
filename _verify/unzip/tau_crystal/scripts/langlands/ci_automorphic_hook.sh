#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$ROOT" || exit 1
mkdir -p .tau_ledger/receipts analysis analysis/plots

# ---- gates & budgets ----
: "${CI_AUTOMORPHIC:=1}"
: "${S_PAD:=50000}" ; : "${T_PAD:=50000}"
: "${S_STEP:=2000}" ; : "${T_STEP:=2000}"
: "${CI_AUTOMORPHIC_BUDGET:=45s}"
TIMEOUT=""; command -v timeout >/dev/null 2>&1 && TIMEOUT="timeout $CI_AUTOMORPHIC_BUDGET"
[ "$CI_AUTOMORPHIC" = 1 ] || { echo "[ci-auto] disabled (CI_AUTOMORPHIC=0)"; exit 0; }

# ---- helpers ----
readv(){ f="$1"; k="$2"; sed -n "s/^${k}=\\(.*\\)$/\\1/p" "$f" 2>/dev/null | head -n1; }
min(){ a="$1"; b="$2"; [ "$a" -lt "$b" ] && echo "$a" || echo "$b"; }
max(){ a="$1"; b="$2"; [ "$a" -gt "$b" ] && echo "$a" || echo "$b"; }
sha256(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d' ' -f1
  else echo ""; fi
}

# ---- seed witnesses ----
[ -x scripts/langlands/seed_witness_envs.sh ] && bash scripts/langlands/seed_witness_envs.sh || true
best_env="analysis/reciprocity_best.env"
sec_env="analysis/reciprocity_second.env"
S1="$(readv "$best_env" BEST_S_MICRO)"; T1="$(readv "$best_env" BEST_T_MICRO)"
S2="$(readv "$sec_env"  BEST_S_MICRO)"; T2="$(readv "$sec_env"  BEST_T_MICRO)"
[ -n "$S1$T1" ] || { echo "[ci-auto] no primary witness; aborting gracefully"; exit 0; }
: "${S2:=$S1}"; : "${T2:=$T1}"

# bounds
S_MIN=$(( $(min "$S1" "$S2") - S_PAD )); S_MAX=$(( $(max "$S1" "$S2") + S_PAD ))
T_MIN=$(( $(min "$T1" "$T2") - T_PAD )); T_MAX=$(( $(max "$T1" "$T2") + T_PAD ))

# ---- sweep ----
scan="analysis/bash_theta_scan.tsv"
if [ -x scripts/langlands/theta_scan_proxy2.sh ]; then
  S_PAD="$S_PAD" T_PAD="$T_PAD" S_STEP="$S_STEP" T_STEP="$T_STEP" $TIMEOUT \
  bash scripts/langlands/theta_scan_proxy2.sh || true
elif [ -x scripts/langlands/around_witness_scan.sh ]; then
  S_PAD="$S_PAD" T_PAD="$T_PAD" S_STEP="$S_STEP" T_STEP="$T_STEP" $TIMEOUT \
  bash scripts/langlands/around_witness_scan.sh || true
else
  echo "[ci-auto] no scanner found; skipping sweep"
fi

# ---- minima & plots ----
[ -x scripts/langlands/morse2d_pure.sh ] && bash scripts/langlands/morse2d_pure.sh "$scan" || true
[ -x scripts/langlands/basins_map.sh ]   && bash scripts/langlands/basins_map.sh || true
[ -x scripts/langlands/atlas_line.sh ]   && bash scripts/langlands/atlas_line.sh || true

# ---- metrics ----
rows=0; if [ -f "$scan" ]; then rows="$(wc -l < "$scan" 2>/dev/null || echo 0)"; fi
case "$rows" in ''|*[!0-9]* ) rows=0 ;; esac
data_rows=$(( rows>0 ? rows-1 : 0 ))

morse="analysis/morse_crit.tsv"
minima_count=0
if [ -f "$morse" ]; then
  minima_count="$(grep -c $'\tminimum\t' "$morse" 2>/dev/null || true)"
  case "$minima_count" in ''|*[!0-9]* ) minima_count=0 ;; esac
fi

best_delta=""; best_S="$S1"; best_T="$T1"
if [ -f "$morse" ] && [ "$minima_count" -gt 0 ]; then
  # pick smallest Delta among 'minimum' lines (pure bash)
  first=1
  while IFS=$'\t' read -r s t typ delta rest; do
    [ "$first" = 1 ] && { first=0; case "$s" in ''|*[!0-9-]* ) continue;; esac; }
    case "$typ" in *min* )
      case "$delta" in ''|*[!0-9-]* ) continue ;; esac
      if [ -z "$best_delta" ] || [ "$delta" -lt "$best_delta" ]; then
        best_delta="$delta"; best_S="$s"; best_T="$t"
      fi
    ;;
    esac
  done < <(tail -n +2 "$morse")
fi
: "${best_delta:=0}"

# ---- artifact hashes ----
artifact_json=""
for f in \
  "$scan" "$morse" \
  "analysis/atlas_line.tsv" "analysis/plots/atlas_line.svg" \
  "analysis/plots/basins.svg" "analysis/ramanujan.tsv"
do
  [ -f "$f" ] || continue
  sum="$(sha256 "$f")"; [ -n "$sum" ] || continue
  artifact_json="${artifact_json}{\"sha256\":\"$sum\",\"path\":\"$f\"},"
done
artifact_json="[${artifact_json%,}]"

# ---- receipt ----
HEAD_SHORT="$(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
UTC="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
RUNNER="${RUNNER_OS:-$(uname -s)} ${RUNNER_ARCH:-$(uname -m)}"
REC=".tau_ledger/receipts/receipt_${UTC//:/-}_${HEAD_SHORT}.json"

cat > "$REC" <<JSON
{
  "kind": "tau.receipt+langlands",
  "commit": "$HEAD_SHORT",
  "utc": "$UTC",
  "runner": "$RUNNER",
  "langlands": {
    "grid": {
      "rows": $data_rows,
      "bounds": {"S_MIN": $S_MIN, "S_MAX": $S_MAX, "T_MIN": $T_MIN, "T_MAX": $T_MAX},
      "step": {"S": $S_STEP, "T": $T_STEP}
    },
    "minima_count": $minima_count,
    "best": {"S_micro": $best_S, "T_micro": $best_T, "Delta": $best_delta}
  },
  "artifacts": $artifact_json
}
JSON

[ -x scripts/langlands/update_ledger.sh ] && bash scripts/langlands/update_ledger.sh || true

echo "[ci-auto] rows=$data_rows minima=$minima_count best=($best_S,$best_T) Δ=$best_delta"
echo "[ci-auto] receipt: $REC"
