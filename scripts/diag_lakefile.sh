#!/usr/bin/env bash
set -euo pipefail
f="${1:-lakefile.lean}"
[ -f "$f" ] || { echo "[err] not found: $f"; exit 1; }

echo "[file] $f"
echo "[stat] size=$(wc -c <"$f") bytes  lines=$(wc -l <"$f")"
sha256sum "$f" 2>/dev/null || true

# detect CRLF
if grep -q $'\r' "$f"; then
  echo "[crlf] CRLF line endings detected"
else
  echo "[crlf] LF only"
fi

# show lines containing backticks
echo "[scan] lines with backticks:"
awk '/`/ {printf("[line %d] %s\n", NR, $0)}' "$f" || true

# show any code-fence lines
echo "[scan] code fences:"
grep -nE '^\s*```' "$f" || echo "[ok] no code fences"

# show possible non-ASCII control chars (excluding tab/newline)
echo "[scan] control chars:"
grep -nP '[\x00-\x08\x0B\x0C\x0E-\x1F]' "$f" || echo "[ok] none"

# show context around the first two offending lines (if any)
first=$(awk '/`/{print NR; exit}' "$f" || true)
second=$(awk 'f&&/`/{print NR; exit}{if(/`/)f=1}' "$f" || true)
for n in $first $second; do
  [ -n "$n" ] || continue
  echo "[context] around line $n"
  awk -v L="$n" 'NR>=L-3 && NR<=L+3 {printf("%5d | %s\n", NR, $0)}' "$f"
done
