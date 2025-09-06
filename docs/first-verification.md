# First verification in 90 seconds

This demo shows τ-Crystal catching a deliberate divergence and pointing at the exact lines that changed.

## 1) Emit a receipt
./scripts/emit-receipt.sh
cp out/manifest.json out/manifest-A.json

## 2) Flip one knob and emit again
TAU_SEED=99 ./scripts/emit-receipt.sh
cp out/manifest.json out/manifest-B.json

## 3) See the difference
git diff --no-index -- out/manifest-A.json out/manifest-B.json || true

You should see `tau_series` and `rank_kernel` differ and the
`timestamp_utc` advance. That’s the “first red vs green” moment τ-Crystal
surfaces in CI on every PR.
