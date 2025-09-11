#!/usr/bin/env bash
set -Eeuo pipefail
set +H
umask 022

fail(){ echo "[fail] $*"; exit 1; }
warn(){ echo "[warn] $*"; }
ok(){ echo "[ok] $*"; }

# sha256 helper: sha256sum or openssl fallback
sha256(){
  if command -v sha256sum >/dev/null 2>&1; then sha256sum; else openssl dgst -sha256 | awk "{print \$2}"; fi
}

T="docs/MONOGRAPH.md"
[ -s "$T" ] || fail "missing $T"

echo "[info] spec guard: verifying test vector, chain-head, and merkle equality"

# --- Check 1: canonical test-vector digest matches exactly as printed ---
J=$(grep -E -m1 '^\{"producer":"tau-crystal 1\.2\.0",' "$T" || true)
[ -n "$J" ] || fail "canonical JSON test vector not found in $T"
H=$(printf %s "$J" | sha256 | awk "{print \$1}")
EXP="f5db69aa83a74d8f774ec3e54a12da5359a37df782821c274268429c1f373b86"
[ "$H" = "$EXP" ] || fail "test vector digest mismatch: got $H expected $EXP"
ok "test vector digest matches ($H)"

# --- Check 2: chain-head line format and receipt hash correctness ---
CH=".tau_ledger/chain.head"
if [ ! -f "$CH" ]; then
  alt=$(ls -1t .tau_ledger/*.head 2>/dev/null | head -n1 || true)
  [ -n "$alt" ] && CH="$alt"
fi
if [ -f "$CH" ]; then
  last=$(awk 'NF{keep=$0} END{print keep}' "$CH")
  [ -n "$last" ] || fail "empty chain-head: $CH"
  printf %s "$last" | grep -q $'\r' && fail "CR detected in chain-head (must be LF only): $CH"
  echo "$last" | grep -Eq '^[0-9a-f]{64} [^[:space:]]+$' || fail "invalid chain-head format (expect: 64-hex, single space, relative path): $last"
  set -- $last
  CHASH="$1"
  RPATH="$2"
  [ -f "$RPATH" ] || fail "receipt path not found: $RPATH"
  RHASH=$(cat "$RPATH" | sha256 | awk "{print \$1}")
  [ "$RHASH" = "$CHASH" ] || fail "receipt hash mismatch: chain=$CHASH file=$RHASH"
  ok "chain-head formatting and receipt hash verified ($RPATH)"
else
  warn "no chain-head present; skipping chain checks"
fi

# --- Check 3: receipt.reflective.merkle_root == some manifest.merkle_root ---
if [ -f "${RPATH:-}" ]; then
  rc_json=$(tr -d '\r\n' < "$RPATH")
  RMR=$(printf %s "$rc_json" | grep -oE '"reflective"[[:space:]]*:[[:space:]]*\{[^}]*"merkle_root"[[:space:]]*:[[:space:]]*"[0-9a-f]{64}"' | head -n1 | sed -E 's/.*"([0-9a-f]{64})".*/\1/' || true)
  [ -n "$RMR" ] || fail "reflective.merkle_root not found in receipt: $RPATH"
  match=0
  while IFS= read -r -d "" f; do
    m=$(tr -d '\r' < "$f" | grep -oE '"merkle_root"[[:space:]]*:[[:space:]]*"[0-9a-f]{64}"' | head -n1 | sed -E 's/.*"([0-9a-f]{64})".*/\1/' || true)
    if [ -n "$m" ] && [ "$m" = "$RMR" ]; then match=1; echo "[info] matched manifest: $f"; break; fi
  done < <(find .tau_ledger -type f -name "*.json" -print0 2>/dev/null)
  [ "$match" -eq 1 ] || fail "no manifest with merkle_root=$RMR found under .tau_ledger"
  ok "receipt.reflective.merkle_root matches a manifest.merkle_root ($RMR)"
else
  warn "no receipt path available; skipping merkle equality check"
fi

ok "spec guard completed successfully"
