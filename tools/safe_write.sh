#!/usr/bin/env bash
set -euo pipefail
dest="${1:?usage: safe_write.sh <dest>}"
shift || true
tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
cat > "$tmp"

# Normalize CRLF -> LF
sed -i 's/\r$//' "$tmp"

case "$dest" in
  *.sh)
    # basic shell syntax check
    if ! bash -n "$tmp"; then echo "[err] bash -n failed for $dest"; exit 3; fi
    mode=0755
    ;;
  *.yml|*.yaml)
    # YAML/Action lint if available; never blocks if missing
    if command -v actionlint >/dev/null 2>&1; then
      actionlint -color never -shellcheck= -oneline "$tmp" || { echo "[err] actionlint failed for $dest"; exit 4; }
    fi
    mode=0644
    ;;
  *)
    mode=0644
    ;;
esac

install -Dm"$mode" "$tmp" "$dest"
echo "[ok] wrote: $dest"
