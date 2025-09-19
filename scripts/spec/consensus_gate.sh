#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
mode="${TAU_CONSENSUS:-3}"
ok_bash=1; ok_lean=1; ok_rust=1
bash scripts/ops/verify_offline.sh >/dev/null 2>&1 && ok_bash=0 || ok_bash=$?
if command -v lake >/dev/null 2>&1; then lake exe verify-chain >/dev/null 2>&1 && ok_lean=0 || ok_lean=$?; else ok_lean=127; fi
if [ -x ./tau_verify ]; then ./tau_verify . >/dev/null 2>&1 && ok_rust=0 || ok_rust=$?; else ok_rust=127; fi
count=0; [ "$ok_bash" = 0 ] && count=$((count+1)); [ "$ok_lean" = 0 ] && count=$((count+1)); [ "$ok_rust" = 0 ] && count=$((count+1))
need=3; [ "$mode" = "any" ] && need=1; [ "$mode" = "2" ] && need=2
if [ "$count" -ge "$need" ]; then echo "[consensus] OK ($count/$need)"; exit 0; fi
mkdir -p analysis; R=analysis/consensus_diff.txt; : > "$R"
printf "bash_verify: %s\nlean_verify: %s\nrust_verify: %s\n" "$ok_bash" "$ok_lean" "$ok_rust" >> "$R"
echo "[consensus] FAIL ($count/$need). See $R"; exit 9
