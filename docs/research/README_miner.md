# HEO Relation Miner (Research Track)

- **Runner:** `./ci/heo/research/run_miner.sh`
- **Output:** `receipts/heo/discovered/`
  - `index.json` — all emitted receipts
  - `unique_index.json` — deduplicated signatures
- **Verification:** Each receipt carries a `verify_relation.py` test (non-blocking CI).

Stable receipt IDs: `heo.discovered.<seq_basename>_<type>_<n>`.
