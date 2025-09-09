#!/usr/bin/env bash
set -euo pipefail
KEY="$1"
: "${CAS_S3_BUCKET:?set CAS_S3_BUCKET repo secret}"
: "${CAS_S3_PREFIX:=lean-cache}"
: "${AWS_DEFAULT_REGION:=us-east-1}"
OBJ="s3://${CAS_S3_BUCKET}/${CAS_S3_PREFIX}/${KEY}.tar.gz"
echo "[pull] $OBJ"
if aws s3 ls "$OBJ" >/dev/null 2>&1; then
  rm -rf .lake/build
  mkdir -p .lake/build
  aws s3 cp "$OBJ" - | tar -xzf -
  echo "[pull] cache restored"
else
  echo "[pull] miss"
fi
