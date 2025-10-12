#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
git ls-files -z | xargs -0 sha256sum | sort -k2,2
