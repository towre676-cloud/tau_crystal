#!/usr/bin/env bash
set -euo pipefail
OWNER="towre676-cloud"
REPO="tau_crystal"
WORKFLOWS=$(gh api "repos/$OWNER/$REPO/actions/workflows" --jq '.workflows[].path' | sed 's#.*/###')
cat > README.md << "EOF"
# τ-Crystal

The project certifies not merely outputs but execution paths. Every build binds a geometric tau-clock to a Lean 4 program and emits a compact, cryptographically stable manifest that can be replayed, diffed, and audited without ambiguity. The result is a proof-carrying runtime receipt for scientific compute: identical inputs, identical path, identical proof. If two runs diverge, the manifest makes the point of divergence explicit and machine-checkable, collapsing weeks of forensics into a deterministic, one-line comparison. The repository is intentionally small and strict. Lake orchestrates the Lean toolchain; the executable graph emits a canonical receipt; the CI harness fixes the invariant grammar so that a receipt from today can be inspected tomorrow and still verify byte-for-byte.
EOF
{ echo; while read -r wf; do [ -n "$wf" ] && printf '![CI: %s](https://github.com/%s/%s/actions/workflows/%s/badge.svg?branch=main)\n' "$wf" "$OWNER" "$REPO" "$wf"; done <<< "$WORKFLOWS"; echo; } >> README.md
cat >> README.md << "EOF"
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
EOF
