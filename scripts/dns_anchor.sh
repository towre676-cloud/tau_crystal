#!/usr/bin/env bash
# One-liner to publish Merkle root as DNS TXT under tau-crystal.yourdomain.com
# Requires: dig + DNS write access
DOMAIN="${DOMAIN:-tau-crystal.yourdomain.com}"
MERKLE=$(jq -r .merkle_root tau-crystal-manifest.json)
echo "Publish this TXT record:"
echo "_tau-crystal-chunk IN TXT \"merkle=$MERKLE timestamp=$(date -u +%Y%m%d-%H%M%S)\""
