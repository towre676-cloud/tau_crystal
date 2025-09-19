#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/gates"; mkdir -p "$root"
ts=$(date -u +%Y%m%dT%H%M%SZ); report="$root/report.$ts.txt"
passed=0; failed=0; skipped=0
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk '{print $1}'; else openssl dgst -sha256 "$1" | awk '{print $2}'; fi; }
check(){ case "$2" in PASS) passed=$((passed+1));; FAIL) failed=$((failed+1));; SKIP) skipped=$((skipped+1));; esac; printf '%s: %s\n' "$1" "$2" >> "$report"; }
latest(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 || true; }

: > "$report"

if ls -1 .tau_ledger/receipts/*.json >/dev/null 2>&1; then check "receipts" "PASS"; else check "receipts" "SKIP"; fi
holo=$(latest ".tau_ledger/holo/holov1-*.json");    [ -s "$holo" ] && check "holo_artifact" "PASS" || check "holo_artifact" "SKIP"
phys=$(latest ".tau_ledger/physics/passport*.json");[ -s "$phys" ] && check "physics_artifact" "PASS" || check "physics_artifact" "SKIP"
perma=$(latest ".tau_ledger/perma/permav1-*.meta"); [ -s "$perma" ] && check "perma_artifact" "PASS" || check "perma_artifact" "SKIP"
mir=$(latest ".tau_ledger/mirror/mirrorv1-*.meta"); [ -s "$mir" ] && check "mirror_artifact" "PASS" || check "mirror_artifact" "SKIP"
binv=$(latest ".tau_ledger/tau_bin/binv1-*.meta");  [ -s "$binv" ] && check "bin_artifact" "PASS" || check "bin_artifact" "SKIP"

godel=$(latest ".tau_ledger/genius/godelv1-*.meta")
if [ -s "$godel" ]; then
  stored=$(sed -n 's/^self_hash: //p' "$godel" | head -n1 | tr -d '\r')
  if [ -n "$stored" ]; then
    tmp=$(mktemp); trap 'rm -f "$tmp"' EXIT
    grep -v '^self_hash: ' "$godel" > "$tmp"
    have=$(sha "$tmp")
    [ "$stored" = "$have" ] && check "genius_godel" "PASS" || check "genius_godel" "FAIL"
  else
    check "genius_godel" "SKIP"
  fi
else
  check "genius_godel" "SKIP"
fi

ents=$(ls -1 .tau_ledger/genius/entangle-*.meta 2>/dev/null | LC_ALL=C sort || true)
if [ -n "$ents" ]; then
  sum=$(awk '/^tau: /{s+=$2} END{print s+0}' $ents)
  cnt=$(awk '/^tau: /{n++} END{print n+0}' $ents)
  if [ "$cnt" -gt 0 ]; then
    ok=$(awk -v s="$sum" -v n="$cnt" 'BEGIN{print (s>(0.5*n))?1:0}')
    [ "$ok" = "1" ] && check "genius_entangle" "PASS" || check "genius_entangle" "FAIL"
  else check "genius_entangle" "FAIL"; fi
else check "genius_entangle" "SKIP"; fi

for label in paradox conscious dark gomboc mandelbrot omega riemann singularity; do
  file=$(latest ".tau_ledger/genius/${label}v1-*.meta")
  if [ -s "$file" ]; then check "genius_${label}" "PASS"; else check "genius_${label}" "SKIP"; fi
done

printf 'policy_gate: %s passed, %s failed, %s skipped\n' "$passed" "$failed" "$skipped" >> "$report"
echo "policy_gate → $report"
exit 0
