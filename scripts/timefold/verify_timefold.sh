#!/usr/bin/env bash
# lines: 27
# Verify latest timefold archive against its meta.
set -Eeuo pipefail; set +H; umask 022
root=".tau_ledger/timefolds"
meta="${1:-$(ls -1 "$root"/tf-*.meta 2>/dev/null | LC_ALL=C sort | tail -1 || true)}"
[ -n "$meta" ] && [ -f "$meta" ] || { echo "usage: $0 [tf-*.meta]" >&2; exit 2; }
sha(){ scripts/meta/_sha256.sh "$1"; }

arc="$(awk '/^archive:/{print $2}' "$meta")"
want="$(awk '/^sha256:/{print $2}' "$meta")"
[ -f "$arc" ] || { echo "[FAIL] missing archive: $arc" >&2; exit 1; }

have="$(sha "$arc")"
if [ "$have" = "$want" ]; then
  echo "[OK] timefold verified (sha256:$have)"
else
  echo "[FAIL] timefold hash mismatch"; echo " want: $want"; echo " have: $have"; exit 1
fi
