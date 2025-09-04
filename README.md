# τ-Crystal

The project certifies not merely outputs but execution paths. Every build binds a geometric tau-clock to a Lean 4 program and emits a compact, cryptographically stable manifest that can be replayed, diffed, and audited without ambiguity. The result is a proof-carrying runtime receipt for scientific compute: identical inputs, identical path, identical proof. If two runs diverge, the manifest makes the point of divergence explicit and machine-checkable, collapsing weeks of forensics into a deterministic, one-line comparison. The repository is intentionally small and strict. Lake orchestrates the Lean toolchain; the executable graph emits a canonical receipt; the CI harness fixes the invariant grammar so that a receipt from today can be inspected tomorrow and still verify byte-for-byte.

![CI: assure.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/assure.yml/badge.svg?branch=main)
![CI: ci.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/ci.yml/badge.svg?branch=main)
![CI: codeql.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/codeql.yml/badge.svg?branch=main)
![CI: ledger-tau.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/ledger-tau.yml/badge.svg?branch=main)

Getting started is a two-command path on any machine with a recent toolchain. First, install elan (which supplies Lean and Lake) and confirm the versions; second, build the library and invoke a single assurance script that emits a canonical manifest. The same commands run in CI and on your desktop so the attestation story is uniform.

```bash
# one-time toolchain (Git Bash)
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
lean --version
lake --version

# repo root: build and assure
lake build
./scripts/assure.sh
```
