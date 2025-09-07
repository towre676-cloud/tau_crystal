#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022
OUT_TSV="${1:-assumption_census.tsv}"
OUT_SUM="${GITHUB_STEP_SUMMARY:-}"
TMP="$(mktemp -t census.XXXXXX || mktemp -u)"
: > "$OUT_TSV"
printf "%s\t%s\t%s\t%s\n" "kind" "file" "line" "text" >> "$OUT_TSV"
files="$(git ls-files "*.lean" 2>/dev/null || true)"
axi=0; opa=0; uns=0; ext=0
for f in $files; do
  # axiom / opaque
  grep -nE "^[[:space:]]*(axiom|opaque)\\b" "$f" 2>/dev/null | while IFS=: read -r ln txt; do
    kind="$(printf "%s" "$txt" | sed -E "s/^[[:space:]]*(axiom|opaque).*/\\1/")"
    [ "$kind" = "axiom" ] && axi=$((axi+1)) || opa=$((opa+1))
    printf "%s\t%s\t%s\t%s\n" "$kind" "$f" "$ln" "$(printf "%s" "$txt" | sed -E "s/[[:space:]]+/ /g")" >> "$OUT_TSV"
  done
  # unsafe def/theorem/etc.
  grep -nE "^[[:space:]]*unsafe[[:space:]]+(def|theorem|abbrev|inductive|structure)\\b" "$f" 2>/dev/null | while IFS=: read -r ln txt; do
    uns=$((uns+1))
    printf "%s\t%s\t%s\t%s\n" "unsafe" "$f" "$ln" "$(printf "%s" "$txt" | sed -E "s/[[:space:]]+/ /g")" >> "$OUT_TSV"
  done
  # extern FFI via @[extern]
  grep -nE "@\\[extern\\]" "$f" 2>/dev/null | while IFS=: read -r ln txt; do
    ext=$((ext+1))
    printf "%s\t%s\t%s\t%s\n" "extern" "$f" "$ln" "$(printf "%s" "$txt" | sed -E "s/[[:space:]]+/ /g")" >> "$OUT_TSV"
  done
done
tot=$((axi+opa+uns+ext))
sha_toolchain="$(tr -d \"\\r\" < lean-toolchain 2>/dev/null | tr -s \"[:space:]\" \" \" | sed -E \"s/^[[:space:]]+|[[:space:]]+\$//g\" | sha256sum 2>/dev/null | awk '{print $1}' || echo none)"
if [ -n "$OUT_SUM" ] && [ -w "$OUT_SUM" ]; then
  printf "### Assumption census\\n" >> "$OUT_SUM"
  printf "toolchain sha256: %s\\n\\n" "$sha_toolchain" >> "$OUT_SUM"
  printf "axiom: %d\\nopaque: %d\\nunsafe: %d\\nextern: %d\\n(total: %d)\\n" "$axi" "$opa" "$uns" "$ext" "$tot" >> "$OUT_SUM"
fi
mv -f "$OUT_TSV" .tau_ledger/assumption_census.tsv 2>/dev/null || cp -f "$OUT_TSV" .tau_ledger/assumption_census.tsv
rm -f "$TMP" 2>/dev/null || true
echo "[census] axioms=$axi opaque=$opa unsafe=$uns extern=$ext total=$tot"
