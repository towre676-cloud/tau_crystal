#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
logdir=".tau_ledger/runlogs"; mkdir -p "$logdir"
ok=0; bad=0
note(){ printf "%s %s\n" "$(date -u +%Y%m%dT%H%M%SZ)" "$1" | tee -a "$logdir/run.log"; }
run(){ local name="$1"; shift; if [ $# -eq 0 ]; then return 0; fi; note "[run] $name"; if "$@" >> "$logdir/$name.out" 2>> "$logdir/$name.err"; then note "[ok ] $name"; ok=$((ok+1)); else note "[bad] $name"; bad=$((bad+1)); fi; }
exists(){ [ -f "$1" ] && [ -r "$1" ]; }
exe(){ [ -x "$1" ]; }
ensure_receipt(){
  if ls -1 .tau_ledger/receipts/*.json >/dev/null 2>&1; then return 0; fi
  local t; t=$(date -u +%Y%m%dT%H%M%SZ); local r=".tau_ledger/receipts/demo-$t.json"
  : > "$r"; printf "%s\n" "{" >> "$r"
  printf "%s\n" "  \"commit\": \"demo-$t\"," >> "$r"
  printf "%s\n" "  \"merkle_root\": \"deadbeef\"," >> "$r"
  printf "%s\n" "  \"wrapper_digest\": \"beadfeed\"," >> "$r"
  printf "%s\n" "  \"tau_tensor\": \"none\"," >> "$r"
  printf "%s\n" "  \"entropy_delta_bytes\": 0" >> "$r"
  printf "%s\n" "}" >> "$r"
  note "[seed] created $r"
}
try_script(){ local label="$1"; local path="$2"; shift 2; if ! exists "$path"; then return 0; fi; if exe "$path"; then run "$label" "$path" "$@"; else run "$label" bash "$path" "$@"; fi; }
main(){
  ensure_receipt
  local wit; wit=$(ls -1 .tau_ledger/receipts/*.json | LC_ALL=C sort | tail -1)
  try_script "holo_build" "scripts/holo/build_holo_tensor.sh"
  try_script "holo_stamp" "scripts/holo/stamp_holo_into_manifest.sh"
  try_script "holo_verify" "scripts/holo/verify_holo_tensor.sh"
  if exists "scripts/tools/cp_residual_symm_verifier.py"; then run "phys_symm" python "scripts/tools/cp_residual_symm_verifier.py" ".tau_ledger/physics/passport.json"; fi
  if exists "scripts/tools/delta27_verifier.py"; then run "phys_delta27" python "scripts/tools/delta27_verifier.py" ".tau_ledger/physics/passport.json"; fi
  try_script "phys_stamp" "scripts/tools/stamp_physics_into_manifest.sh"
  try_script "perma_pin" "scripts/perma/pin_receipt_to_ipfs.sh" "$wit"
  try_script "perma_stamp" "scripts/perma/stamp_perma_into_manifest.sh"
  try_script "perma_verify" "scripts/perma/verify_perma_receipt.sh"
  if command -v curl >/dev/null 2>&1; then remote="https://raw.githubusercontent.com/towre676-cloud/tau_crystal/main"; try_script "mirror_fetch" "scripts/mirror/mirror_receipts.sh" "$remote"; fi
  try_script "mirror_stamp" "scripts/mirror/stamp_mirror_into_manifest.sh"
  try_script "mirror_verify" "scripts/mirror/verify_mirror_receipts.sh"
  ts=$(date -u +%Y%m%dT%H%M%SZ)
  if exists "scripts/cache/mathlib_cache.py"; then run "cache_log" python "scripts/cache/mathlib_cache.py" log ".tau_ledger/cache/cache-$ts.json"; fi
  if exists "scripts/cache/mathlib_cache.py"; then run "cache_predict" python "scripts/cache/mathlib_cache.py" predict ".tau_ledger/cache/cache-$ts.json"; fi
  try_script "cache_stamp" "scripts/cache/stamp_cache_into_manifest.sh"
  if exists "scripts/evolver/tau_evolver.py"; then run "evolver" python "scripts/evolver/tau_evolver.py" ".tau_ledger/cache/cache-$ts.json" ".tau_ledger/evolver/evolver-$ts.json"; fi
  try_script "evolver_stamp" "scripts/evolver/stamp_evolver_into_manifest.sh"
  try_script "bin_verify" "scripts/tau_bin/tau_verify.sh" "$wit"
  try_script "bin_stamp" "scripts/tau_bin/stamp_bin_into_manifest.sh"
  try_script "gen_godel" "scripts/genius/godel_self_verify.sh"
  try_script "gen_entangle" "scripts/genius/quantum_entangle.sh" 2
  try_script "gen_verify_ent" "scripts/genius/verify_entanglement.sh"
  try_script "gen_paradox" "scripts/genius/temporal_paradox.sh" "20260914T000000Z"
  try_script "gen_conscious" "scripts/genius/consciousness_imprint.sh"
  try_script "gen_dark" "scripts/genius/dark_matter_verify.sh" "classified"
  try_script "gen_gomboc" "scripts/genius/gomboc_computation.sh"
  try_script "gen_mandel" "scripts/genius/mandelbrot_receipt.sh" "tau-crystal-infinitum"
  try_script "gen_omega" "scripts/genius/omega_point.sh"
  try_script "gen_riemann" "scripts/genius/riemann_foundation.sh" 42
  try_script "gen_singularity" "scripts/genius/singularity_seed.sh" 100
  try_script "gen_unified" "scripts/genius/genius_unified.sh"
  if command -v docker >/dev/null 2>&1 && exists "scripts/meta/docker_receipt_label.sh"; then run "docker_label" bash "scripts/meta/docker_receipt_label.sh" "$wit" docker/Dockerfile; else note "[skip] docker label"; fi
  if exists "scripts/gates/policy_gate.sh"; then try_script "policy_gate" "scripts/gates/policy_gate.sh"; fi
  note "[done] safe run: $ok ok, $bad bad"; [ "$bad" -eq 0 ]
}
main "$@"
