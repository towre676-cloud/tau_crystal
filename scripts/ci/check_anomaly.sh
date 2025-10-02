#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
exec "$(dirname "$0")/check_anomaly_glue.sh"
