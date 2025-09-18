#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
root="$(pwd)"
build="build"; atlas="analysis/atlas.jsonl"
M="$build/_manifest.json"
[ -s "$M" ] || { echo "[mint] missing $M" >&2; exit 4; }

# Try to parse; if any key is empty, recompute from build/ deterministically
grab() { sed -n "s/.*\"$1\":\"\([^\"]\+\)\".*/\1/p" "$M" | head -n1; }
build_hash="$(grab build_hash)"
data_hash="$(grab data_hash)"
ts="$(grab ts)"
commit="$(grab commit)"

recalc=false
if [ -z "$build_hash" ] || [ -z "$data_hash" ] || [ -z "$ts" ] || [ -z "$commit" ]; then
  recalc=true
  data_hash="$("$root/scripts/meta/_sha256.sh" "$build/data/atlas.jsonl")"
  tmp="$(mktemp)"
  ( cd "$build" && find . -type f -print0 | sort -z | while IFS= read -r -d '' f; do
      rel="${f#./}"
      h="$("$root/scripts/meta/_sha256.sh" "$build/$rel")"
      printf "%s  %s\n" "$h" "$rel"
    done ) > "$tmp"
  build_hash="$("$root/scripts/meta/_sha256.sh" "$tmp")"
  rm -f "$tmp"
  ts="$(date -u +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || echo 1970-01-01T00:00:00Z)"
  commit="$(git rev-parse --short=12 HEAD 2>/dev/null || echo nogit)"
fi

# Emit receipt (fixed key order, compact)
mkdir -p .tau_ledger/dashboard
R=".tau_ledger/dashboard/dashboard_${ts//[:]/-}.json"; : > "$R"
printf "%s" "{"                                         >> "$R"
printf "%s" "\"schema\":\"taucrystal/dashboard/v1\","   >> "$R"
printf "%s" "\"build_hash\":\"$build_hash\","           >> "$R"
printf "%s" "\"data_hash\":\"$data_hash\","             >> "$R"
printf "%s" "\"commit\":\"$commit\","                   >> "$R"
printf "%s" "\"ts\":\"$ts\""                            >> "$R"
printf "%s\n" "}"                                       >> "$R"

# Atlas stamp (append-only)
printf "%s\n" "{\"type\":\"DASHBOARD\",\"build_hash\":\"$build_hash\",\"data_hash\":\"$data_hash\",\"ts\":\"$ts\"}" >> "$atlas"

# Deterministic witness tarball of the build/
tmplist="$(mktemp)"
( cd "$build" && find . -type f -print0 | sort -z | xargs -0 printf "%s\n" ) > "$tmplist"
pack="witness-dashboard-${ts//[:]/-}-${build_hash:0:12}.tar.gz"
( cd "$build" && tar -czf "../$pack" --owner=0 --group=0 --format=ustar -T "$tmplist" ) || { echo "[mint] tar failed"; rm -f "$tmplist"; exit 9; }
rm -f "$tmplist"

[ "$recalc" = true ] && echo "[mint] manifest parse failed; recomputed hashes" || true
echo "[mint] receipt + $pack"
