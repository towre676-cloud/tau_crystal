#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C

ID="${1:-auto-$(date -u +%Y%m%dT%H%M%SZ)}"
OUT="analysis/capsules/$ID"; mkdir -p "$OUT"
TMP_TAR=".tau_ledger/capsules/$ID.tar.gz"  # write tar OUTSIDE what we archive
TAR="$OUT/$ID.tar.gz"
MAN="$OUT/manifest.json"
REC="$OUT/capsule.receipt.json"

# 0) gates must be green
scripts/capsules/verify.sh >/dev/null

# 1) build the archive
INCLUDE=()
[ -d analysis ] && INCLUDE+=("analysis")
[ -d docs ] && INCLUDE+=("docs")
if [ ${#INCLUDE[@]} -eq 0 ]; then
  echo "[PACKAGE] nothing to include (no analysis/ or docs/)" >&2
  exit 2
fi

mkdir -p .tau_ledger/capsules
tar -czf "$TMP_TAR" \
  --exclude="analysis/capsules" \
  --exclude=".tau_ledger" \
  "${INCLUDE[@]}"

# 2) move archive into capsule dir (now it can't self-include)
mv -f "$TMP_TAR" "$TAR"

# 3) hash
sha256sum "$TAR" | awk '{print $1}' > "$TAR.sha256"
SHA=$(cat "$TAR.sha256")

# 4) manifest (minimal, extend as needed)
cat > "$MAN" <<JSON
{"capsule":"$ID","hash_sha256":"$SHA","created_utc":"$(date -u +%Y-%m-%dT%H:%M:%SZ)","provenance":"auto"}
JSON

# 5) project receipt (for Attested Delivery)
cat > "$REC" <<JSON
{"type":"capsule_receipt","capsule":"$ID","hash_sha256":"$SHA","manifest":"$MAN"}
JSON

printf "[PACKAGE] %s\n%s\n" "$TAR" "$SHA"
