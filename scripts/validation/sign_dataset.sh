#!/usr/bin/env bash
set -euo pipefail; set +H
bin="${1:?usage: sign_dataset.sh <SIGNED_DATASET.bin> <corridor.receipt.tsv>}"
out="${2:?usage: sign_dataset.sh <SIGNED_DATASET.bin> <corridor.receipt.tsv>}"
mkdir -p "$(dirname "$out")"
H="$(sha256sum "$bin" | awk '{print $1}')"
ts="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
{
  echo "time\t$ts"
  echo "dataset\t$bin"
  echo "sha256\t$H"
  echo "op_return_hex\t6a20$H"
  echo "broadcast_instructions\tuse your wallet to push OP_RETURN with this data"
} > "$out"
echo "$H"
