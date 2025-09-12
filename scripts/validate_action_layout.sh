#!/usr/bin/env bash
set +H; umask 022
ok=1
check(){ [ -e "$1" ] || { echo "[MISS] $1"; ok=0; }; }
check action.yml
check scripts/tau_verify.sh
check scripts/spec_guard.sh
check scripts/tau_adapter.sh
check scripts/tau_sweep.sh
check scripts/tau_fuse.sh
check scripts/bin/pav.awk
[ "$ok" -eq 1 ] && echo "[PASS] action layout looks good" || { echo "[ERR] fix the above paths"; exit 1; }
