#!/usr/bin/env bash
set -euo pipefail
REC="${RECEIPT_PATH:-.tau_ledger/receipt.json}"
STMT="${STATEMENT_FILE:-lake-manifest.json}"
GRAM="${GRAMMAR_FILE:-verify/ReceiptGrammar.lean}"
[ -s "$REC" ] || { echo "[err] receipt missing: $REC"; exit 2; }
[ -s "$STMT" ] || { echo "[warn] statement missing: $STMT"; STMT=""; }

r_hash="$(scripts/hash.sh "$REC"   | awk '{print $1}')"
s_hash="$( [ -n "$STMT" ] && scripts/hash.sh "$STMT" | awk '{print $1}' || echo "")"
g_hash="$(scripts/grammar_hash.sh | awk '{print $1}')"

run_id="${GITHUB_RUN_ID:-0}"
ts="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
repo="${GITHUB_SERVER_URL:-https://github.com}/${GITHUB_REPOSITORY:-unknown}"
commit="$(git rev-parse HEAD 2>/dev/null || echo unknown)"

line=$(printf '{"version":"tlog-1","timestamp":"%s","repo":"%s","commit":"%s","run_id":"%s","receipt_blake3":"%s","statement_blake3":"%s","grammar_blake3":"%s"}' \
       "$ts" "$repo" "$commit" "$run_id" "$r_hash" "$s_hash" "$g_hash")

leaf="$r_hash"   # default leaf material; Trillian may return a different leaf
root=""
ots_file=""

# A) Trillian (preferred)
if [ -n "${TLOG_URL:-}" ]; then
  auth=()
  [ -n "${TLOG_API:-}" ] && auth=(-H "Authorization: Bearer ${TLOG_API}")
  resp="$(printf '%s' "$line" | curl -fsS "${auth[@]}" -H 'Content-Type: application/json' \
          -X POST "${TLOG_URL%/}/entries" -d @- || true)"
  if [ -n "$resp" ]; then
    root="$(printf '%s' "$resp" | sed -n 's/.*"root"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -n1)"
    l2="$(printf '%s' "$resp" | sed -n 's/.*"leaf"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -n1)"
    [ -n "$l2" ] && leaf="$l2"
    echo "[ok] tlog(trillian) root=$root leaf=$leaf"
  else
    echo "[warn] trillian POST failed; falling back"
  fi
fi

# B) Gist append (best-effort)
if [ -z "$root" ] && [ -n "${TLOG_GIST_ID:-}" ]; then
  tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
  gh gist view "$TLOG_GIST_ID" --files --raw > "$tmp" 2>/dev/null || true
  touch "$tmp"
  printf '%s\n' "$line" >> "$tmp"
  gh gist edit "$TLOG_GIST_ID" -a "$tmp#tlog.ndjson"
  echo "[ok] tlog(gist) appended"
fi

# C) Local NDJSON (always)
mkdir -p .tau_ledger
printf '%s\n' "$line" >> .tau_ledger/tlog.ndjson
echo "[ok] tlog(local) appended -> .tau_ledger/tlog.ndjson"

# Anchor via OpenTimestamps when available (anchors SHA256 of the evidence line)
if python3 - <<'PY' >/dev/null 2>&1; then
    import sys,hashlib
PY
then
  p="$(mktemp)"; printf '%s\n' "$line" > "$p"
  if python3 -m pip show opentimestamps-client >/dev/null 2>&1; then
    ots=".tau_ledger/tlog_$(date -u +%Y%m%dT%H%M%SZ).ots"
    python3 -m opentimestamps_client.cli stamp "$p" >/dev/null 2>&1 || true
    python3 -m opentimestamps_client.cli upgrade "$p.ots" >/dev/null 2>&1 || true
    [ -f "$p.ots" ] && mv "$p.ots" "$ots" && ots_file="$ots" && echo "[ok] ots -> $ots"
  fi
fi

# Export for caller (GitHub step needs these)
printf 'TLOG_LEAF=%s\nTLOG_ROOT=%s\nOTS_FILE=%s\n' "$leaf" "$root" "$ots_file" > .tau_ledger/tlog-last.env
