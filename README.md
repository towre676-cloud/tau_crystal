# tau_crystal

Deterministic diagnostic runner with `cert`, `τ-pulse`, and `qCRO` lines, a signed JSON manifest, and linear-time work probes.

[![assure](https://github.com/towre676-cloud/tau_crystal/actions/workflows/assure.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/assure.yml)

---

## Quickstart

### Bash (Linux/macOS or Git Bash on Windows)
```bash
# Build
$HOME/.elan/bin/lake.exe build

# Run once
$HOME/.elan/bin/lake.exe exe tau_crystal -- \
  --tau 1.25 \
  --q "0,0.5,1,2" \
  --run-id demo \
  --out manifest.json \
  --audit true
