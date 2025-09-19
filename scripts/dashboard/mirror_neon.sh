#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
# Requires $DATABASE_URL (psql) and a table schema that fits your JSON lines.
[ -n "$DATABASE_URL" ] || { echo "[neon] set DATABASE_URL" >&2; exit 2; }
jsonl="build/data/atlas.jsonl"
[ -s "$jsonl" ] || { echo "[neon] missing $jsonl" >&2; exit 4; }
# Example: shove JSONL into a staging table with one jsonb column.
psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -c 'CREATE TABLE IF NOT EXISTS atlas_jsonl(line jsonb); TRUNCATE atlas_jsonl;'
psql "$DATABASE_URL" -v ON_ERROR_STOP=1 -c "\copy atlas_jsonl(line) FROM '$jsonl' WITH (FORMAT text);"
echo "[neon] mirrored $jsonl"
