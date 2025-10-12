#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
bash scripts/lf_sanitize.sh scripts/*.sh README.md docs/METHODS.md 2>/dev/null || true
bash scripts/compose_methods_precis.sh
bash scripts/compose_readme_receipts.sh
git add docs/METHODS.md README.md scripts/compose_*sh scripts/lf_sanitize.sh 2>/dev/null || true
git commit -m "docs: METHODS precis + receipts; enforce LF endings" || true
git push || true
