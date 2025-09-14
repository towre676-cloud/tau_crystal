#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
logdir=".tau_ledger/runlogs"; mkdir -p "$logdir"; ok=0; bad=0
note(){ printf "%s %s\n" "$(date -u +%Y%m%dT%H%M%SZ)" "$1" | tee -a "$logdir/run.log"; }
exists(){ [ -f "$1" ] && [ -r "$1" ]; }
exe(){ [ -x "$1" ]; }
run(){ local name="$1"; shift; note "[run] $name"; if "$@" >> "$logdir/$name.out" 2>> "$logdir/$name.err"; then note "[ok ] $name"; ok=$((ok+1)); else note "[bad] $name"; bad=$((bad+1)); fi; }
try(){ local label="$1" path="$2"; shift 2; if ! exists "$path"; then note "[skip] $label"; return; fi; if exe "$path"; then run "$label" "$path" "$@"; else run "$label" bash "$path" "$@"; fi; }
ensure_receipt(){ if ls -1 .tau_ledger/receipts/*.json >/dev/null 2>&1; then return 0; fi; t=$(date -u +%Y%m%dT%H%M%SZ); r=".tau_ledger/receipts/demo-$t.json"; : > "$r"; printf "%s\n" "{" >> "$r"; printf "%s\n" "  \"commit\": \"demo-$t\"," >> "$r"; printf "%s\n" "  \"merkle_root\": \"deadbeef\"," >> "$r"; printf "%s\n" "  \"wrapper_digest\": \"beadfeed\"," >> "$r"; printf "%s\n" "  \"tau_tensor\": \"none\"," >> "$r"; printf "%s\n" "  \"entropy_delta_bytes\": 0" >> "$r"; printf "%s\n" "}" >> "$r"; note "[seed] $r"; }
main(){
  ensure_receipt; wit=$(ls -1 .tau_ledger/receipts/*.json | LC_ALL=C sort | tail -1)
  try "holo_build" "scripts/holo/build_holo_tensor.sh"
  try "holo_stamp" "scripts/holo/stamp_holo_into_manifest.sh"
  try "phys_stamp" "scripts/tools/stamp_physics_into_manifest.sh"
  try "perma_pin"  "scripts/perma/pin_receipt_to_ipfs.sh" "$wit"
  try "perma_stamp" "scripts/perma/stamp_perma_into_manifest.sh"
  remote="https://raw.githubusercontent.com/towre676-cloud/tau_crystal/main"; try "mirror_fetch" "scripts/mirror/mirror_receipts.sh" "$remote"
  try "mirror_stamp" "scripts/mirror/stamp_mirror_into_manifest.sh"
  try "cache_stamp" "scripts/cache/stamp_cache_into_manifest.sh"
  try "evolver_stamp" "scripts/evolver/stamp_evolver_into_manifest.sh"
  try "bin_verify" "scripts/tau_bin/tau_verify.sh" "$wit"
  try "bin_stamp"  "scripts/tau_bin/stamp_bin_into_manifest.sh"
  try "gen_godel"       "scripts/genius/godel_self_verify.sh"
  try "gen_entangle"    "scripts/genius/quantum_entangle.sh" 2
  try "gen_verify_ent"  "scripts/genius/verify_entanglement.sh"
  try "gen_paradox"     "scripts/genius/temporal_paradox.sh" 20260914T000000Z
  try "gen_conscious"   "scripts/genius/consciousness_imprint.sh"
  try "gen_dark"        "scripts/genius/dark_matter_verify.sh" classified
  try "gen_gomboc"      "scripts/genius/gomboc_computation.sh"
  try "gen_mandel"      "scripts/genius/mandelbrot_receipt.sh" tau-crystal-infinitum
  try "gen_omega"       "scripts/genius/omega_point.sh"
  try "gen_riemann"     "scripts/genius/riemann_foundation.sh" 42
  try "gen_singularity" "scripts/genius/singularity_seed.sh" 100
  try "gen_unified"     "scripts/genius/genius_unified.sh"
  try "policy_gate" "scripts/gates/policy_gate.sh"
  note "[done] $ok ok, $bad bad"; [ "$bad" -eq 0 ]
}
main "$@"
