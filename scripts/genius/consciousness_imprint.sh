#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
. scripts/genius/_util.sh
root=".tau_ledger/genius"; mkdir -p "$root"
t=$(ts); f="$root/consciousv1-$t.meta"
set +e; files=$(ls -1 "$root"/entangle-*.meta 2>/dev/null); rc=$?; set -e
[ $rc -eq 0 ] && [ -n "$files" ] || { echo "[err] no entangle files"; exit 2; }
read avg var cnt < <(awk '/^tau: /{v=$2; s+=v; ss+=v*v; n++} END{ if(n>0){m=s/n; print m, (ss/n)-(m*m), n}else{print 0,0,0}}' $files)
: > "$f"
emit_kv schema taucrystal/conscious/v1 "$f"
emit_kv id "$(basename "${f%.meta}")" "$f"
emit_kv utc "$t" "$f"
emit_kv variance "$var" "$f"
det=$(awk -v v="$var" 'BEGIN{print (v<0.001)?1:0}')
emit_kv is_deterministic "$det" "$f"
echo "[OK] conscious: $f"
[ "$det" = "1" ] || { echo "[FAIL] variance too high"; exit 1; }
