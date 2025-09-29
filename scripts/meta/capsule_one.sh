#!/usr/bin/env bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C

BASE=".tau_ledger/lean_module_capsules"
TMP=".cache/capsules"
mkdir -p "$BASE" "$TMP" exe/.capsule_each

rel="${1:-}"; [ -n "$rel" ] || { echo "[err] missing arg"; exit 2; }
[ -f "$rel" ] || { echo "[err] missing: $rel"; exit 2; }
case "$rel" in ./*) rel="${rel#./}";; esac
mod="${rel%.lean}"; mod="${mod//\//.}"

hfile="exe/.capsule_each/${rel//\//_}"
mkdir -p "$(dirname "$hfile")"
cp -f "$rel" "$hfile"

impt="$TMP/_imports.$$"
grep -E "^[[:space:]]*import[[:space:]]" "$rel" | sed -E "s/^[[:space:]]*import[[:space:]]+//" | tr -d "\r" > "$impt" || true

start_ns=$(date +%s%N 2>/dev/null || echo 0)
build_log="$TMP/_build_${mod//./_}.log"; : > "$build_log"
build_ok=0
tmp_olean="$TMP/_tmp_${mod//./_}.olean"
if lake env lean -o "$tmp_olean" "$hfile" >"$build_log" 2>&1; then build_ok=1; fi

end_ns=$(date +%s%N 2>/dev/null || echo 0)
dur_ms=0; if [ "$start_ns" != 0 ] && [ "$end_ns" != 0 ]; then dur_ms=$(( (end_ns - start_ns)/1000000 )); fi

sha256_file () {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}";
  elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | awk "{print \$1}";
  else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi
}

src_sha=$(sha256_file "$rel")
src_bytes=$(wc -c < "$rel" | tr -d "[:space:]")

olean_sha="NONE"; olean_bytes=0
if [ -f "$tmp_olean" ]; then
  olean_sha=$(sha256_file "$tmp_olean")
  olean_bytes=$(wc -c < "$tmp_olean" | tr -d "[:space:]")
fi

tc=$(lake env lean --version 2>/dev/null | head -n1 || echo "lean:unknown")
lv=$(lake --version 2>/dev/null | head -n1 || echo "lake:unknown")
last_commit=$(git log -n1 --format=%H -- "$rel" 2>/dev/null || echo "unknown")
run_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)

imps="[]"
if [ -s "$impt" ]; then
  imps="["; sep=""
  while IFS= read -r imp; do
    printf -v imps "%s%s\"%s\"" "$imps" "$sep" "$imp"
    sep=","
  done < "$impt"
  imps="${imps}]"
fi

out="$BASE/${mod//./_}.json"; : > "$out"

{
  echo "{"
  echo "  \\"module\\": \\"$mod\\","
  echo "  \\"path\\": \\"$rel\\","
  echo "  \\"imports\\": $imps,"
  echo "  \\"src_sha256\\": \\"$src_sha\\","
  echo "  \\"src_bytes\\": $src_bytes,"
  echo "  \\"olean_sha256\\": \\"$olean_sha\\","
  echo "  \\"olean_bytes\\": $olean_bytes,"
  echo "  \\"build_ok\\": $build_ok,"
  echo "  \\"build_time_ms\\": $dur_ms,"
  echo "  \\"toolchain\\": \\"$tc\\","
  echo "  \\"lake\\": \\"$lv\\","
  echo "  \\"last_commit\\": \\"$last_commit\\","
  echo "  \\"run_utc\\": \\"$run_utc\\""
  echo "}"
} > "$out"

echo "[capsule] $mod build_ok=$build_ok ms=$dur_ms"
