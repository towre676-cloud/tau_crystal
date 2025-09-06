[![Plan: FREE](https://img.shields.io/badge/plan-FREE-blue?style=flat-square)](./.tau_plan_roots.env)
[![CI](https://img.shields.io/github/actions/workflow/status/towre676-cloud/tau_crystal.git/verify.yml?style=flat-square)](https://github.com/towre676-cloud/tau_crystal.git/actions)
[![Attestation](https://img.shields.io/badge/attestation-ledger-green?style=flat-square)](./.tau_ledger/attestation.txt)


# τ-Crystal

## Plans

**τ‑Crystal** is free for public repos and small private experiments.  
**Pro** ($12k/year) turns it into an org-grade verification spine:

- Organization-wide SSO and policy enforcement
- 10× CI throughput with formal proof gates required
- 180-day manifest retention, Merkle root stamping
- Receipt chain with immutable attestation export

If your auditors, insurers, or treasury depend on this, you want **Pro**.


[![Live τ](https://img.shields.io/badge/gh--pages-live%20τ-blue)](https://towre676-cloud.github.io/tau_crystal/sample/live.html)  
[Monograph](https://towre676-cloud.github.io/tau_crystal/MONOGRAPH/) · 
[Repository](https://github.com/towre676-cloud/tau_crystal)

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

The project certifies not merely outputs but execution paths. Every build binds a geometric tau-clock to a Lean 4 program and emits a compact, cryptographically stable manifest that can be replayed, diffed, and audited without ambiguity. The result is a proof-carrying runtime receipt for scientific compute: identical inputs, identical path, identical proof. If two runs diverge, the manifest makes the point of divergence explicit and machine-checkable, collapsing weeks of forensics into a deterministic, one-line comparison. The repository is intentionally small and strict. Lake orchestrates the Lean toolchain; the executable graph emits a canonical receipt; the CI harness fixes the invariant grammar so that a receipt from today can be inspected tomorrow and still verify byte-for-byte.

![CI: assure.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/assure.yml/badge.svg?branch=main)
![CI: ci.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/ci.yml/badge.svg?branch=main)
![CI: codeql.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/codeql.yml/badge.svg?branch=main)
![CI: ledger-tau.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/ledger-tau.yml/badge.svg?branch=main)

Getting started is a two-command path on any machine with a recent toolchain. First, install elan (which supplies Lean and Lake) and confirm the versions; second, build the library and invoke a single assurance script that emits a canonical manifest. The same commands run in CI and on your desktop so the attestation story is uniform.

```bash
# one-time toolchain (Git Bash)

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
lean --version
lake --version

# repo root: build and assure

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
lake build
./scripts/assure.sh
```

---
Read the monograph: [docs/MONOGRAPH.md](docs/MONOGRAPH.md)

---

[![Receipt Verified](https://img.shields.io/badge/tau--crystal-receipt--verified-brightgreen?logo=github)](docs/manifest.md)

[![τ‑Crystal Verified](https://img.shields.io/badge/receipt-verified-brightgreen?logo=github)](docs/manifest.md)

[![receipt-verified](https://img.shields.io/badge/receipt-verified-brightgreen)](https://towre676-cloud.github.io/tau_crystal/tau-crystal.html)

—

See **[CI Pipeline](docs/CI.md)** · **[License](LICENSE)** · **[Sample HTML](docs/sample/live.html)**

## Quickstart

```bash
# from repo root
bash scripts/plan/tau_pro_gate.sh
bash scripts/plan/write_roots.sh
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-20} ./scripts/plan/launch_verifiers.sh
```

- Latest status: see `docs/manifest.md` (STATUS + MERKLE_ROOT)
- Receipts: `.tau_ledger/receipts/`
- Chain head: `.tau_ledger/CHAIN`
- Human summary: `.tau_ledger/attestation.txt`


## Docs

- **Manifest spec**: `docs/specs/manifest-v1.1.md` (if present)
- **Live manifest**: `docs/manifest.md`
- **Ledger attestation**: `.tau_ledger/attestation.txt`
- **Audit guide**: `docs/AUDIT.md`
- **CI notes**: `docs/ci.md`

