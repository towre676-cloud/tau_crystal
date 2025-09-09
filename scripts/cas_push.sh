#!/usr/bin/env bash
set -euo pipefail
KEY="$1"
: "${CAS_S3_BUCKET:?set CAS_S3_BUCKET repo secret}"
: "${CAS_S3_PREFIX:=lean-cache}"
TAR="$(mktemp)"
tar -czf "$TAR" .lake/build
aws s3 cp "$TAR" "s3://${CAS_S3_BUCKET}/${CAS_S3_PREFIX}/${KEY}.tar.gz"
rm -f "$TAR"
echo "[push] uploaded ${KEY}.tar.gz"
