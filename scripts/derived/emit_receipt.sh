#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
ROOT="analysis/derived"
REC="analysis/derived/receipts"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
MAP="$REC/derived.$STAMP.map"
HASH="$REC/derived.$STAMP.hash"
OUT="$REC/derived.$STAMP.receipt.json"
mkdir -p "$REC"
: > "$MAP"
find "$ROOT" -type f ! -path "*/receipts/*" | LC_ALL=C sort > "$MAP"
: > "$HASH"
while IFS= read -r P; do scripts/meta/_sha256.sh "$P" >> "$HASH"; done < "$MAP"
: > "$OUT"
python - "$STAMP" "$HASH" "$OUT" <<PY
import sys, json, hashlib
stamp, hash_path, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
entries = []
with open(hash_path, "r", encoding="utf-8", errors="ignore") as f:
    for line in f:
        parts = line.strip().split(maxsplit=1)
        if not parts: continue
        h = parts[0]
        p = parts[1] if len(parts) > 1 else ""
        entries.append({"sha256": h, "path": p})
m = hashlib.sha256()
for e in entries: m.update(e["sha256"].encode("ascii", "ignore"))
doc = {
  "id": "D_B5-of-Chamber",
  "stamp": stamp,
  "merkle": m.hexdigest(),
  "files": entries
}
with open(out_path, "w", encoding="utf-8") as g: json.dump(doc, g, indent=2)
print(out_path)
PY
