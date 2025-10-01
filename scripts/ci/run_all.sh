#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
cd "$(dirname "$0")/../.." || exit 1
bash scripts/ci/_sanitize_canons.sh
bash scripts/ci/check_anomaly_glue.sh
bash scripts/ci/check_modular.sh
bash scripts/ci/check_specnet.sh
bash scripts/ci/check_chamber.sh
bash scripts/ci/check_padic.sh
bash scripts/ci/check_sset.sh
