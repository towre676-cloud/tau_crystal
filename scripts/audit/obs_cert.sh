#!/usr/bin/env bash
set -e; set +H; umask 022
scripts/obs/obs_cert_emit.sh >/dev/null 2>&1 || true
cat artifacts/obs/obs_certificate.json
