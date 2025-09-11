# Contributing to τ-Crystal

1. Fork and branch: `git checkout -b feat/xyz`
2. Run the verifier locally:
   ```bash
   bash scripts/verify_release_state.sh
   ```
3. Add tests/receipts if behavior changes; keep CHAIN and manifest consistent.
4. Open a PR; CI must pass (receipt/manifest checks run in Actions).

## Fast-path CI
- Root-only changes → `ci-fast` at repo root.
- Single top-level module with `ci-fast` → `make -C <module> ci-fast`.
- Anything else → full build (`lake build`).
To enable fast-path in a module:  
`bash scripts/ci/install_ci_fast.sh <dir> rust|python|go|node`
