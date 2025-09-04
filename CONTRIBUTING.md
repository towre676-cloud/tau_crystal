# Contributing to τ-Crystal

Small fixes (docs/typos) → open a PR. Larger changes → start a Discussion with the problem and approach.

Local setup: install elan and Lean 4. Toolchain is pinned to `leanprover/lean4:v4.22.0`.
Build and quick check from repo root:
- `lean --version`
- `lake --version`
- `lake build`
- `./scripts/assure.sh` → writes `out/manifest.json` and `out/fusion.stdout.txt`

Style: keep changes small and readable. If you touch the receipt format, explain why the canonical grammar is preserved (or how it evolves).

Commits/PRs: imperative messages (`fix:`, `feat:`, `docs:`). Open PRs against `main`. CI (Tau Crystal Assure) must pass and still upload the `tau-crystal-manifest` artifact with `manifest.json`.

License: by contributing, you agree your changes are MIT-licensed with the repo. If you need DCO, add `Signed-off-by: Name <email>` to your commits.
