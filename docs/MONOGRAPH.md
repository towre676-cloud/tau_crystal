τ‑Crystal

A canonical receipt for any computation—from a single script run to a planet‑scale ERP flow. One line emits the proof. One hash binds the truth.

---

## Affidavit, not artifact

Every execution should carry a small, deterministic receipt—something that tells you where two runs align, where they diverge, or whether they’re provably equivalent. τ‑Crystal is that receipt: a live algebraic trace recorded in real time, structured as a certificate, and verified on commit. It replaces timestamp soup with calibrated time. It replaces logging glue with contract‑stable state vectors. It replaces best‑effort attestation with content‑addressed, re‑checkable manifests.

---

## Live digest

```json
{
  "manifests": 42,
  "latest_root": "sha256:7d0f1c9e4a…",
  "signed": true,
  "built_at": "2025-09-06T14:20:11Z"
}
Fast track
bash
Copy code
# Build + emit a manifest
lake build
TAU_SLOPE=0.30 TAU_MIN=0.06 scripts/rebuild-from-file.sh tmp/P2P.ndjson

# Verify entire chain
scripts/verify-all.sh

# Optional: render live HTML
python scripts/publish-html.py
Receipt schema (stable since 1.2.0)
json
Copy code
{
  "kind": "tau-crystal-receipt",
  "version": "1.2.0",
  "process": {
    "id": "PO-2025-0912-00421",
    "domain": "P2P",
    "segment": "GRN.posted",
    "prev_manifest": "sha256:5e8c…"
  },
  "tau": {
    "t": [0.0, 0.41, 0.77, 1.05],
    "clock": "Chebyshev-decay",
    "params": { "tau_min": 0.25, "lead_prior_days": 7 }
  },
  "residue": {
    "R_norm": 0.083,
    "D_norm": 0.017,
    "kappa": 0.1591549431,
    "qcro": [{ "t": 1.05, "mode": "split_receipt", "amp": 0.62 }]
  },
  "witness": {
    "events_sha": "sha256:9ad1…",
    "pivot_transcript": "sha256:3b72…",
    "rank_signature": { "p": 2147482951, "rank": 6 }
  },
  "sustainability": {
    "co2e_kg": 128.4,
    "lane_id": "LAX→DFW",
    "contract_sla": "sha256:ccaa…"
  },
  "attest": {
    "merkle_root": "sha256:7d0f…",
    "signed_by": "ed25519:org-key-2025",
    "timestamp": "2025-09-06T14:20:11Z"
  }
}
JSON byte equality is receipt identity. Whitespace is canonical. Optional fields disappear. One manifest equals one executable truth.

Same receipt, different scale
A single R&D run or an enterprise‑wide ERP both fit the same shape. The grammar never changes. The clock just gets smarter.

Domain	τ‑observable	Residue signal	Certificate payload	Decision surface
Procure‑to‑Pay	PO→GRN→Match→AP→Payment; vendor lead‑time, lane delay, inspection mix	Match friction, late mass, rework q‑CRO spikes	Rank signature over match matrix, carbon tags, SLA witness	Cash release, vendor reroute, expediting price, stock update
Order‑to‑Cash	Quote→Order→ATP→Pick/Pack→POD→Invoice	Dwell torsion, carrier slippage	Carrier leg proof, POD attestation, chargeback rank	Promise date replan, carrier incentives, slotting changes
Production/MES	Job→Issue→Start→Complete→QC; setup graph, cycle priors	Scrap resonance, micro‑stoppages	Route proof, QC cert, OEE ranks	Dispatch, SMED targeting, energy‑aware scheduling
FP&A / Treasury	Plan→Commit→Actuals; ladder from AP/AR clocks	Forecast drift, liquidity modes	Cash ladder rank cert, hedge linkage	Rolling forecast, working capital playbook
Workforce	Requisition→Hire→Ramp→Retention	Ramp curvature, attrition wavefronts	Skill witness, ramp path	Shift design, retention incentive vector

The contract
ERP emits canonical events: PurchaseOrderCreated, GoodsReceived, InvoiceApproved, and peers. The τ‑Crystal sidecar listens, builds its vector clock, measures the deformation, and writes a digest‑only manifest. The ERP transaction proceeds; no blocking. All you store is the pointer hash. All you replay is the receipt itself. Every system sees the same signal.

Governance, verified
SOX gets full‑path attestation. ESG gets CO₂ and defect scores tied to real flow. Insurers get algebraic variance, not best‑effort categories. Vendors get scored lanes, not QBR anecdotes. The same manifest satisfies all of them without API bloat, vendor lock, or audit drag.

Security posture
Manifests are Ed25519‑signed. Merkle roots are SHA‑256‑locked. No secrets stored. No source persisted. CI verifies the manifest chain using a read‑only GitHub App identity. Everything that touches a receipt is verifiable, minimal, and content‑addressed.

Adoption: one step at a time
Start with Procure‑to‑Pay. You already have the events. Add a short Python or Bash sidecar. Let it emit receipts to manifests/. Drop the verifier into CI. Watch it turn red when match logic gets patchy; watch it turn green when flow stabilizes. Then add Order‑to‑Cash, then MES, then FP&A. No flags, no platform wars. Just receipts.

Formal interface (Lean 4)
lean
Copy code
structure TauCrystal.Manifest where
  kind           : String
  version        : String
  process        : Json
  tau            : Json
  residue        : Json
  witness        : Json
  sustainability : Json
  attest         : Json
deriving FromJson, ToJson

def loadLatestManifest : IO Manifest := do
  let files ← System.FilePath.readDir "manifests"
  let latest := files.map (·.path) |>.qsort (toString · > toString ·) |>.get! 0
  let raw ← IO.FS.readFile latest
  match fromJson? <| Json.parse raw with
  | .ok m      => pure m
  | .error err => throw <| IO.userError s!"parse error: {err}"
You can now prove theorems about tau, residue, or merkle_root using the same manifest the verifier uses. Your execution trace becomes part of your formal reasoning system.

The deal
Keep the schema boring. Keep the receipts small. Keep the checks visible. A green check means the path was valid. A red one means it wasn’t. You don’t need another dashboard. You need one manifest that proves what really happened.
