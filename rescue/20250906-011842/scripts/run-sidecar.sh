#!/usr/bin/env bash
set -u
DOMAIN="${1:-P2P}"
TOPIC="${2:-erp.events.P2P}"
if [ -f sidecar/.venv/Scripts/activate ]; then . sidecar/.venv/Scripts/activate
elif [ -f sidecar/.venv/bin/activate ]; then . sidecar/.venv/bin/activate
fi
: "${TAU_MIN:=0.05}"
: "${TAU_SLOPE:=0.25}"
scripts/erp-subscribe.sh "$DOMAIN" "$TOPIC" | python sidecar/tau_sidecar.py | python sidecar/sign_manifest.py manifests
