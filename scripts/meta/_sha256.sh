#!/usr/bin/env bash
set -euo pipefail
git ls-files -z | xargs -0 sha256sum | sort -k2
