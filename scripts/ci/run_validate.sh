#!/usr/bin/env bash
set -euo pipefail
echo "=== Structural validation ==="
./scripts/ci/validate_certificates.sh
echo "=== Semantic validation ==="
python3 scripts/ci/semantic_check.py
echo "=== Hash verification ==="
python3 scripts/ci/hash_check.py
echo "=== All checks passed ==="
