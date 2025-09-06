#!/usr/bin/env bash
set -euo pipefail
ROOT="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }
fail(){ printf "[FAIL] %s\n" "$1" >&2; exit 1; }
ok(){ printf "[OK] %s\n" "$1"; }
[ -s ".tau_ledger/CHAIN" ] || fail ".tau_ledger/CHAIN not found"
head_hash=$(awk "END{print \$1}" .tau_ledger/CHAIN || true)
rcpt_path=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN || true)
[ -n "$head_hash" ] || fail "empty CHAIN"
[ -n "$rcpt_path" ] && [ -f "$rcpt_path" ] || fail "receipt not found: $rcpt_path"
calc_hash=$(sha256sum "$rcpt_path" | awk "{print \$1}")
[ "$calc_hash" = "$head_hash" ] || fail "chain head mismatch (calc=$calc_hash, head=$head_hash)"
ok "chain head = $head_hash (receipt = $rcpt_path)"
man_json="tau-crystal-manifest.json"; man_md="docs/manifest.md"; m=""
if [ -s "$man_json" ]; then
  if command -v jq >/dev/null 2>&1; then m=$(jq -r ".merkle_root // empty" "$man_json");
  else m=$(awk "{if (match(\$0, /\\\"merkle_root\\\"[[:space:]]*:[[:space:]]*\\\"([0-9a-fA-F]{64})\\\"/, a)) {print a[1]; exit}}" "$man_json"); fi
elif [ -s "$man_md" ]; then
  m=$(grep -iE "^MERKLE_ROOT:[[:space:]]*[0-9a-fA-F]{64}" "$man_md" | awk -F: "{gsub(/^[[:space:]]+/,\"\",\$2); print \$2}" | tr -d "[:space:]")
else
  fail "manifest missing: expected tau-crystal-manifest.json or docs/manifest.md"
fi
[ -n "$m" ] || fail "could not read MERKLE_ROOT from manifest"
if command -v jq >/dev/null 2>&1; then
  r=$(jq -r ".reflective.merkle_root // .merkle_root // empty" "$rcpt_path")
else
  r=$(awk "{if (match(\$0, /\\\"merkle_root\\\"[[:space:]]*:[[:space:]]*\\\"([0-9a-fA-F]{64})\\\"/, a)) {print a[1]; exit}}" "$rcpt_path")
fi
[ -n "$r" ] || fail "could not read merkle_root from receipt"
ml=$(printf "%s" "$m" | tr "[:upper:]" "[:lower:]")
rl=$(printf "%s" "$r" | tr "[:upper:]" "[:lower:]")
[ "$ml" = "$rl" ] || fail "manifest.merkle_root != receipt.merkle_root (m=$m, r=$r)"
ok "merkle_root = $m (manifest ↔ receipt)"
