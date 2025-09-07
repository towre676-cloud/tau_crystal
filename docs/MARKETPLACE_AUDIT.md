# Marketplace Auditor Checklist — τ‑Crystal

Enforcement (Pro vs Free)
- Free: runs with proofs optional.
  bash scripts/plan/tau_pro_gate.sh
  bash scripts/plan/write_roots.sh
  TAU_MAX_SHARDS=4 ./scripts/plan/launch_verifiers.sh || true
- Pro: first run blocks unless overridden; second run allowed with override.
  PLAN_OVERRIDE=PRO bash scripts/plan/tau_pro_gate.sh
  PLAN_OVERRIDE=PRO bash scripts/plan/write_roots.sh
  TAU_MAX_SHARDS=4 ./scripts/plan/launch_verifiers.sh && echo should-block || echo blocked-as-expected
  ALLOW_NO_PROOFS=1 TAU_MAX_SHARDS=4 ./scripts/plan/launch_verifiers.sh

Ledger + Manifest
- docs/manifest.md contains MERKLE_ROOT and STATUS
- .tau_ledger/CHAIN last hash equals sha256 of its receipt file
- .tau_ledger/attestation.txt summarizes chain head and recent receipts

Reproducibility
- All scripts bash-only; single CI step runs gate → roots → launcher

Support
Issues: https://github.com/towre676-cloud/tau_crystal/issues
Security: see SECURITY.md
