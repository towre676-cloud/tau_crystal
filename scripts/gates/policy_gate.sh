#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/gates"; mkdir -p "$root"
ts=$(date -u +%Y%m%dT%H%M%SZ); report="$root/report.$ts.txt"
passed=0; failed=0; skipped=0
: > "$report"
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}"; else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi; }
check(){ case "$2" in PASS) passed=$((passed+1));; FAIL) failed=$((failed+1));; SKIP) skipped=$((skipped+1));; esac; printf "%s: %s\n" "$1" "$2" >> "$report"; }
if ls -1 .tau_ledger/receipts/*.json >/dev/null 2>&1; then check "receipts" "PASS"; else check "receipts" "SKIP"; fi
latest(){ ls -1 "$1" 2>/dev/null | LC_ALL=C sort | tail -1 || true; }
holo=$(latest ".tau_ledger/holo/holov1-*.json"); [ -s "$holo" ] && check "holo_artifact" "PASS" || check "holo_artifact" "SKIP"
phys=$(latest ".tau_ledger/physics/passport*.json"); [ -s "$phys" ] && check "physics_artifact" "PASS" || check "physics_artifact" "SKIP"
perma=$(latest ".tau_ledger/perma/permav1-*.meta"); [ -s "$perma" ] && check "perma_artifact" "PASS" || check "perma_artifact" "SKIP"
mirror=$(latest ".tau_ledger/mirror/mirrorv1-*.meta"); [ -s "$mirror" ] && check "mirror_artifact" "PASS" || check "mirror_artifact" "SKIP"
binv=$(latest ".tau_ledger/tau_bin/binv1-*.meta"); [ -s "$binv" ] && check "bin_artifact" "PASS" || check "bin_artifact" "SKIP"
godel=$(latest ".tau_ledger/genius/godelv1-*.meta")
if [ -s "$godel" ]; then
  stored=$(sed -n "s/^self_hash: //p" "$godel" | head -n1)
  tmp=$(mktemp); trap "rm -f \"$tmp\"" EXIT; grep -v "^self_hash: " "$godel" > "$tmp"; have=$(sha "$tmp")
  [ -n "$stored" ] && [ "$stored" = "$have" ] && check "genius_godel" "PASS" || check "genius_godel" "FAIL"
else check "genius_godel" "SKIP"; fi
ents=$(ls -1 .tau_ledger/genius/entangle-*.meta 2>/dev/null | LC_ALL=C sort || true)
if [ -n "$ents" ]; then
  corr=0; n=0; while IFS= read -r f; do v=$(sed -n "s/^tau: //p" "$f" | head -n1); [ -n "$v" ] || continue; corr=$(echo "$corr + $v" | bc -l); n=$((n+1)); done <<< "$ents"
  if [ "$n" -gt 0 ]; then lim=$(echo "$n * 0.5" | bc -l); ok=$(echo "$corr > $lim" | bc -l); [ "$ok" = "1" ] && check "genius_entangle" "PASS" || check "genius_entangle" "FAIL"; else check "genius_entangle" "FAIL"; fi
else check "genius_entangle" "SKIP"; fi
has_kv(){ [ -s "$1" ] && grep -q "^$2: " "$1"; }
p=$(latest ".tau_ledger/genius/paradoxv1-*.meta");  (has_kv "$p" "future" && has_kv "$p" "commitment")  && check "genius_paradox" "PASS" || check "genius_paradox" "${p:+FAIL}"
c=$(latest ".tau_ledger/genius/consciousv1-*.meta"); has_kv "$c" "variance" && check "genius_conscious" "PASS" || check "genius_conscious" "${c:+FAIL}"
d=$(latest ".tau_ledger/genius/darkv1-*.meta");     has_kv "$d" "nullifier" && check "genius_dark" "PASS" || check "genius_dark" "${d:+FAIL}"
g=$(latest ".tau_ledger/genius/gombocv1-*.meta");   has_kv "$g" "stable_state" && check "genius_gomboc" "PASS" || check "genius_gomboc" "${g:+FAIL}"
m=$(latest ".tau_ledger/genius/mandelbrotv1-*.meta");has_kv "$m" "escape_iter" && check "genius_mandelbrot" "PASS" || check "genius_mandelbrot" "${m:+FAIL}"
o=$(latest ".tau_ledger/genius/omegav1-*.meta");    has_kv "$o" "status" && check "genius_omega" "PASS" || check "genius_omega" "${o:+FAIL}"
r=$(latest ".tau_ledger/genius/riemannv1-*.meta");  grep -q "^hypothesis_assumed: true" "$r" 2>/dev/null && check "genius_riemann" "PASS" || check "genius_riemann" "${r:+FAIL}"
s=$(latest ".tau_ledger/genius/singularityv1-*.meta");has_kv "$s" "determinism" && check "genius_singularity" "PASS" || check "genius_singularity" "${s:+FAIL}"
printf "policy_gate: %s passed, %s failed, %s skipped\n" "$passed" "$failed" "$skipped" >> "$report"
echo "policy_gate → $report"
[ "$failed" -eq 0 ] || exit 1
