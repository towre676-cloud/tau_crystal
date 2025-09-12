#!/usr/bin/env bash
set -Eeuo pipefail; set +H
iso_now(){ date -u +%Y-%m-%dT%H:%M:%SZ 2>/dev/null || busybox date -u +%Y-%m-%dT%H:%M:%SZ; }
json_esc(){ sed -e s/\\\\/\\\\\\\\/g -e s/\"/\\\\\"/g; }
join_csv(){ paste -sd, -; }
git_sha(){ git rev-parse --short=12 HEAD 2>/dev/null || echo "unknown"; }
hostname_s(){ hostname 2>/dev/null || echo "unknown"; }
