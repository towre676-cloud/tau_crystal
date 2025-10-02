#!/usr/bin/env bash
set -euo pipefail
OUT="receipts/heo/discovered"
mkdir -p "$OUT"
# Clean previous non-index receipts
find "$OUT" -maxdepth 1 -type f -name "relation_*.json" -delete || true
python3 ci/heo/research/algebraic_relation_engine.py \
  --sequences-glob "ci/data/sequences/*.json" \
  --out-dir "$OUT" \
  --ds "2,3,5" \
  --max-k 16
python3 ci/heo/research/dedupe_relations.py
