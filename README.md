# τ-Crystal — **3× faster Mathlib caching** for Lean CI (Linux, containerized)
![CI: lean-minicache](https://github.com/towre676-cloud/tau_crystal/actions/workflows/lean-minicache.yml/badge.svg?branch=main)

Drop this repo's **`.github/workflows/lean-minicache.yml`** into your project (or copy the fragment). It caches **Mathlib** by exact commit and runs inside a prebuilt Lean container, so PRs on the same Mathlib SHA usually build **3–6× faster**—no registries, no ORAS.

### Quick Start
- Use **Linux runners** only (faster on GitHub-hosted).
- Keep PRs on the **same Mathlib commit** to preserve cache hits.
- Copy or adapt: `.github/workflows/lean-minicache.yml`.
- After two runs (fresh + hydrated), record times in **[docs/BENCHMARK.md](docs/BENCHMARK.md)**.

### What you get
- **Mathlib-only cache** keyed by exact SHA → biggest time win with minimal risk.
- **Prebuilt Lean container** → skips toolchain install (~20–40s saved).
- **Step Summary** prints build time and cache key on every run.

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

## τ-Crystal — proof-carrying runtime manifest for reproducible compute

τ-Crystal turns a repository into a self-verifying project. Every run emits a receipt chained by SHA-256, stamps a repository-wide MERKLE_ROOT over tracked files, and writes a live STATUS line to docs/manifest.md. The result is a one-line, machine-checkable claim you can quote in issues, papers, and audits.

**Why it matters:** traditional pipelines hash outputs or bundle environments, but they don’t prove the execution path. τ-Crystal makes divergence explicit and small: the CHAIN head changes if and only if the verified path changed.

**What you get today (bash-only):**
– Execution-state receipts + CHAIN
– Repository MERKLE_ROOT + manifest STATUS
– Same flow locally and in CI (no containers required)
– Free tier to prove value; Pro adds required proof gates, higher throughput, and longer retention

**Prove it fast:** run the pinned “Verify this release (v0.1.1)” snippet below, then try the Golden diff demo (perturb one tracked file and watch the head change). Keep your science/dev runnable—and provable—without heavy tooling. When you need org-wide enforcement, turn on Pro.


## Verify this release (v0.1.1)

```bash
# fetch and checkout the release tag
git fetch --tags --quiet && git checkout v0.1.1

# run the built-in chain + manifest checks
bash scripts/plan/tau_pro_gate.sh
bash scripts/plan/write_roots.sh
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-4} ./scripts/plan/launch_verifiers.sh

# 1) CHAIN head must match the sha256 of its receipt file
rcpt=$(awk '{p=$2; h=$1} END{print p}' .tau_ledger/CHAIN)
head=$(awk 'END{print $1}' .tau_ledger/CHAIN)
calc=$(sha256sum "$rcpt" | awk '{print $1}')
[ "$calc" = "$head" ] && echo "OK: chain head verified" || echo "FAIL: chain head mismatch"

# 2) Manifest merkle_root must equal receipt.reflective.merkle_root
if command -v jq >/dev/null 2>&1; then
  m="$(jq -r .merkle_root tau-crystal-manifest.json 2>/dev/null)"
  r="$(jq -r .reflective.merkle_root "$rcpt" 2>/dev/null)"
else
  m="$(grep -oE "\"merkle_root\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" tau-crystal-manifest.json | sed -E "s/.*:\"([^\"]*)\".*/\1/" | head -n1)"
  r="$(grep -oE "\"merkle_root\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$rcpt" | head -n1 | sed -E "s/.*:\"([^\"]*)\".*/\1/")"
fi
[ -n "$m" ] && [ "$m" = "$r" ] && echo "OK: manifest ↔ receipt root" || echo "FAIL: root mismatch"
```


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


## Why this is different
Traditional pipelines hash results; **τ‑Crystal hashes the *execution state***.
Each run emits a SHA‑256 chained receipt, stamps a Merkle root over tracked files,
and writes a STATUS line to the manifest. Divergence is not hidden; it’s **explicit,
small, and machine‑checkable** — so you can quote a single line to prove what ran.

## Golden diff (10 lines)
```bash
# 1) baseline receipt
bash scripts/plan/write_roots.sh; TAU_MAX_SHARDS=2 ./scripts/plan/launch_verifiers.sh
base="$(tail -n1 .tau_ledger/CHAIN | awk '{print $1}')" 

# 2) tiny perturbation to a tracked file (no commit); rerun
printf " " >> README.md
bash scripts/plan/write_roots.sh; TAU_MAX_SHARDS=2 ./scripts/plan/launch_verifiers.sh
head="$(tail -n1 .tau_ledger/CHAIN | awk '{print $1}')" 

# 3) print the one‑line diff and revert the perturbation
[ "$base" = "$head" ] && echo "expected a diff, got none" || echo "golden diff: $base -> $head"
git checkout -- README.md
```

## Verify this repo (current commit)

## Why tanh?

- One-soliton: u = 2 ∂_x^2 log(1 + e^θ) collapses to (k^2/2) sech^2(θ/2), with θ = k x + δ at t = 0.
- τ-function (2-soliton): u = 2 ∂_x^2 log τ where τ = det(I + M); after identities the field organizes as sums/products of tanh^2.
- Gudermannian: φ = gd(κ x) maps ℝ to S^1 to place modulation checks on a compact angle.
- Determinism: we hash fixed-point envelopes for cross-OS stability and put hashes in the ledger/manifest.


## Verify soliton demos

```bash
# one-soliton envelope: JSON + hash into .tau_ledger/soliton_envelope.json
bash scripts/run_soliton_envelope.sh
cat .tau_ledger/soliton_envelope.json | (jq -r ".sha256" 2>/dev/null || grep -oE "\"sha256\":\"[0-9a-fA-F]+\"" | sed -E "s/.*:\"([0-9a-fA-F]+)\".*/\1/")
```

```bash
# two-soliton τ/tanh demo: JSON + image (PNG if ImageMagick, else PGM)
bash scripts/run_tau_tanh_demo.sh
cat .tau_ledger/tau_tanh_2soliton.json | (jq -r ".sha256" 2>/dev/null || grep -oE "\"sha256\":\"[0-9a-fA-F]+\"" | sed -E "s/.*:\"([0-9a-fA-F]+)\".*/\1/")
ls -l media/tau_tanh_demo.png 2>/dev/null || echo "open media/tau_tanh_demo.pgm"
```

```bash
# stamp both hashes into docs/manifest.md (idempotent)
bash scripts/stamp_soliton_into_manifest.sh
bash scripts/stamp_tau_tanh_into_manifest.sh
```


Tested at: https://github.com/towre676-cloud/tau_crystal/tree/f9d86ab4714884ff3874de4e5f089f4c40ac25e4

```bash
bash scripts/verify_release_state.sh
```

## Verify this release (cosign)

```bash
# set these for your asset(s)
TAG=v0.1.0
FILE=tau_crystal-$TAG.tgz
DIGEST=sha256:<image-or-asset-digest>

# verify signed SBOM attestation (CycloneDX) for container/image (if published)
cosign verify-attestation --type cyclonedx \n  --certificate-oidc-issuer 'https://token.actions.githubusercontent.com' \n  --certificate-identity 'https://github.com/towre676-cloud/tau_crystal/.github/workflows/release.yml@refs/tags/' \n  ghcr.io/towre676-cloud/tau_crystal@"$DIGEST"

# verify tarball against its .sig + .cert (blob)
cosign verify-blob --certificate "$FILE.cert" --signature "$FILE.sig" "$FILE"
```

## Expected success

```
[OK] chain head = <sha> (receipt = .tau_ledger/receipts/...json)
[OK] merkle_root = <sha> (manifest ↔ receipt)
```


















