#!/usr/bin/env bash
set -euo pipefail
python3 ci/heo/research/algebraic_relation_engine.py \
  --sequences-glob "ci/data/sequences/*.json" \
  --out-dir "receipts/heo/discovered" \
  --ds "2,3,5" \
  --max-k 16
