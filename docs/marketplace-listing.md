# τ‑Crystal — GitHub Marketplace Listing (Copy-Ready)

Tagline
Proof‑carrying verification spine for repos: formal proof gates, receipts, and immutable attestations — all in bash.

Short Description
τ‑Crystal makes your repository self‑verifying. It enforces formal‑proof gates on PRs, stamps a Merkle root over tracked files, emits hash‑linked receipts, and produces a human‑readable attestation — all from CI with bash‑only drop‑ins.

Long Description
- Proof gates on PRs (Lean proofs + receipt chain checks)
- Org‑grade enforcement for Pro: SSO/policy, higher throughput, 180‑day retention
- Receipts + Attestation: hash‑linked JSON receipts, `.tau_ledger/CHAIN`, and `attestation.txt`
- Manifest integrity: `docs/manifest.md` has `MERKLE_ROOT` and live `STATUS`
- Bash‑only: portable, dependency‑light (no container required)

Plans
Free — best for proving value
- Public repos and small private experiments
- 2 verifiers, 14‑day artifact retention
- Proofs optional (non‑blocking)
- Community support

Pro — $12,000/year
- Org‑wide SSO/policy enforcement (SAML/SCIM)
- Unlimited private repos under the org
- 10× CI throughput (e.g., 20 workers)
- 180‑day artifact retention
- Required formal gates on PRs
- Laurent signature + cross‑repo drift diagnostics
- Priority support; SOC‑friendly logs & attestations

Setup
1) Add the app to your org/repo.
2) In CI, run:
   bash scripts/plan/tau_pro_gate.sh
   bash scripts/plan/write_roots.sh
   TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-20} ./scripts/plan/launch_verifiers.sh
3) Review `docs/manifest.md`, `.tau_ledger/attestation.txt`, and `.tau_ledger/receipts/`.

Support
Issues: https://github.com/towre676-cloud/tau_crystal/issues
Security: see SECURITY.md

Legal
Annual prepaid; seats unlimited; policy‑bounded usage. Downgrade at term end; data retention follows new plan. DPA/SOC‑II package available to Pro.
