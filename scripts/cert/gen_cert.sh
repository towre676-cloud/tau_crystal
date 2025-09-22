#!/usr/bin/env bash
set +e; set +H; umask 022

ROOT="$(cd "$(dirname "$0")/../.."; pwd)" || exit 1
cd "$ROOT" || exit 1
CERTDIR="certs"
TS=$(date -u +%Y%m%dT%H%M%SZ)
OUT="$CERTDIR/spectral_cert_$TS"
mkdir -p "$OUT" || exit 1

# files to include
FILES=(
  "spectral_kernel/trace.json"
  "spectral_kernel/face_trace.json"
  "spectral_kernel/trace.png"
  "spectral_kernel/face_trace.png"
)
# include fusion receipts if present
if [ -d "_fusion_out" ]; then
  while IFS= read -r -d '' f; do FILES+=("$f"); done < <(find _fusion_out -type f -print0)
fi

# sha256 helper (sha256sum or python)
hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    python3 - "$1" <<'PY'
import sys, hashlib, pathlib
p = pathlib.Path(sys.argv[1])
print(hashlib.sha256(p.read_bytes()).hexdigest())
PY
  fi
}

MAN="$OUT/MANIFEST.json"
{
  echo '{'
  echo '  "certificate": "craniofacial-spectral",'
  echo "  \"created_utc\": \"$TS\","
  echo '  "git": {'
  echo "    \"commit\": \"$(git rev-parse --short=12 HEAD 2>/dev/null || echo unknown)\","
  echo "    \"remote\": \"$(git remote get-url origin 2>/dev/null | sed 's/\"/\\"/g')\""
  echo '  },'
  echo '  "files": {'
} > "$MAN"

sep=""
root_cat=""

for f in "${FILES[@]}"; do
  [ -f "$f" ] || continue
  h=$(hash_file "$f")
  sz=$(wc -c < "$f" 2>/dev/null | tr -d ' ')
  [ -z "$sep" ] || echo ',' >> "$MAN"
  printf '    "%s": { "sha256": "%s", "bytes": %s }' "$f" "$h" "$sz" >> "$MAN"
  sep=","
  root_cat="${root_cat}${h}\n"
  dst="$OUT/$f"; mkdir -p "$(dirname "$dst")"; cp -p "$f" "$dst"
done

echo '' >> "$MAN"
echo '  },' >> "$MAN"

# root digest = sha256 of sorted concatenated file hashes
if command -v sha256sum >/dev/null 2>&1; then
  root_hash=$(printf "%b" "$root_cat" | LC_ALL=C sort | tr -d '\r\n' | sha256sum | awk '{print $1}')
else
  root_hash=$(python3 - <<'PY'
import sys, hashlib
data = sys.stdin.read()
print(hashlib.sha256(data.encode('utf-8')).hexdigest())
PY
  <<<"$(printf "%b" "$root_cat" | LC_ALL=C sort | tr -d '\r\n')")
fi

echo "  \"root_sha256\": \"$root_hash\"" >> "$MAN"
echo '}' >> "$MAN"

# optional zip (skip if 'zip' missing)
if command -v zip >/dev/null 2>&1; then
  ( cd "$CERTDIR" && zip -qr "$(basename "$OUT").zip" "$(basename "$OUT")" )
fi

echo "[ok] wrote: $OUT"
[ -f "$CERTDIR/$(basename "$OUT").zip" ] && echo "[ok] zip:  $CERTDIR/$(basename "$OUT").zip"
