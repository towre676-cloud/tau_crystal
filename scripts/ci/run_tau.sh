#!/usr/bin/env bash
set -Eeuo pipefail; set +H
TAU_CLASS="${TAU_CLASS:-work}"; case "$TAU_CLASS" in ensemble|work) : ;; *) TAU_CLASS=work ;; esac
R=$(scripts/ci/emit_receipt.sh)
scripts/ci/validate_receipt.sh "$R"
echo "$R"
