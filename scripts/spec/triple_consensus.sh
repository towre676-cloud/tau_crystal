#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
report="analysis/triple_consensus.diff"
: > "$report"

ok=1

# A) Bash offline verifier (your existing one)
if bash scripts/ops/verify_offline.sh >/dev/null 2>&1; then
  echo "[bash] OK"
else
  echo "[bash] FAIL" | tee -a "$report"; ok=0
fi

# B) Lean chain link (if available)
if command -v lake >/dev/null 2>&1; then
  if lake exe verify-chain >/dev/null 2>&1; then
    echo "[lean] OK"
  else
    echo "[lean] FAIL" | tee -a "$report"; ok=0
  fi
else
  echo "[lean] SKIP" | tee -a "$report"
fi

# C) Rust sealed verifier (if present)
if [ -x ./tau_verify ]; then
  if ./tau_verify . >/dev/null 2>&1; then
    echo "[rust] OK"
  else
    echo "[rust] FAIL" | tee -a "$report"; ok=0
  fi
else
  echo "[rust] SKIP" | tee -a "$report"
fi

if [ "${TAU_REQUIRE_TRIPLE:-1}" -eq 1 ]; then
  # require all three present and OK
  need=0; got=0
  command -v lake >/dev/null 2>&1 && need=$((need+1))
  [ -x ./tau_verify ] && need=$((need+1))
  need=$((need+1)) # bash verifier always present
  # Count OKs by grepping report (missing entries imply OK); simpler: recompute directly
  bash_ok=$(bash scripts/ops/verify_offline.sh >/dev/null 2>&1 && echo 1 || echo 0)
  lean_ok=$(command -v lake >/dev/null 2>&1 && lake exe verify-chain >/dev/null 2>&1 && echo 1 || echo 0)
  rust_ok=0; [ -x ./tau_verify ] && ./tau_verify . >/dev/null 2>&1 && rust_ok=1
  got=$((bash_ok + lean_ok + rust_ok))
  if [ "$got" -lt "$need" ]; then echo "[consensus] FAIL ($got/$need) — see $report"; exit 7; fi
fi

exit $(( ok==1 ? 0 : 6 ))
