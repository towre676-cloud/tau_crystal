# CI Notes
- Workflow: `.github/workflows/verify.yml` (launcher → receipt → manifest → attestation)
- Badges: README shows current CI and plan
- Matrix tip: set `fail-fast: false` for complete coverage
- Env flags: `TAU_PLAN`, `TAU_REQUIRE_PROOFS`, `TAU_MAX_WORKERS`, `TAU_RETENTION_DAYS`
