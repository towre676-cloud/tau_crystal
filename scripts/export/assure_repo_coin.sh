#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
REC="${1:-docs/llm_index.v1.json}"
[ -s "$REC" ] || { echo "[assure] index not found: $REC"; exit 2; }
zip_url=$(sed -n 's/.*"zip_url"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$REC" | head -n1)
zip_sha=$(sed -n 's/.*"zip_sha256"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$REC" | head -n1)
commit=$(sed -n 's/.*"git_commit"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$REC" | head -n1)
owner_repo=$(sed -n 's/.*"repo"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$REC" | head -n1)
repo="${owner_repo#*/}"
[ -n "$zip_url" ] && [ -n "$zip_sha" ] && [ -n "$commit" ] && [ -n "$repo" ] || { echo "[assure] missing fields in index"; exit 3; }
dl="_verify/coin.zip"; out="_verify/unzip"; rm -rf "$dl" "$out"; mkdir -p "$out"
echo "[assure] fetching: $zip_url"
curl -fsSL -o "$dl" "$zip_url" || { echo "[assure] download failed"; exit 5; }
if command -v sha256sum >/dev/null 2>&1; then zh=$(sha256sum "$dl" | cut -d" " -f1); else zh=$(shasum -a 256 "$dl" | cut -d" " -f1); fi
[ "$zh" = "$zip_sha" ] || { echo "[assure] sha256 mismatch: got $zh expected $zip_sha"; exit 6; }
unzip -q "$dl" -d "$out" || { echo "[assure] unzip failed"; exit 7; }
prefix="$out/$repo"; [ -d "$prefix" ] || { echo "[assure] expected top folder $repo/ not found"; ls -la "$out"; exit 8; }
tracked_list="_verify/tracked.lst"; zip_list="_verify/zip.lst"; : > "$tracked_list"; : > "$zip_list"
git -c core.autocrlf=false ls-tree -r --name-only "$commit" > "$tracked_list"
( cd "$prefix" && find . -type f -print | sed -E 's#^\./###' | sort ) > "$zip_list"
mismatch=0; checked=0
while IFS= read -r p; do
  [ -z "$p" ] && continue
  checked=$((checked+1))
  f="$prefix/$p"; if [ ! -f "$f" ]; then echo "[assure] missing in zip: $p"; mismatch=$((mismatch+1)); continue; fi
  if command -v sha256sum >/dev/null 2>&1; then
    a=$(git show "$commit:$p" | sha256sum | cut -d" " -f1)
    b=$(sha256sum "$f" | cut -d" " -f1)
  else
    a=$(git show "$commit:$p" | shasum -a 256 | cut -d" " -f1)
    b=$(shasum -a 256 "$f" | cut -d" " -f1)
  fi
  [ "$a" = "$b" ] || { echo "[assure] content mismatch: $p"; mismatch=$((mismatch+1)); }
done < "$tracked_list"
extra_cnt=$(comm -13 <(sort "$tracked_list") <(sort "$zip_list") | wc -l | tr -d " ")
if [ "$extra_cnt" -gt 0 ]; then echo "[assure] extra files present in zip not tracked at $commit: $extra_cnt"; mismatch=$((mismatch+extra_cnt)); fi
if [ "$mismatch" -ne 0 ] || [ "$checked" -eq 0 ]; then
  echo "[assure] FAIL: mismatches=$mismatch, checked=$checked"
  exit 9
fi
AT="analysis/atlas.jsonl"; mkdir -p analysis; touch "$AT"
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
printf "%s\n" "{\"type\":\"EXPORT_ZIP_ASSURED\",\"git_commit\":\"$commit\",\"zip_sha256\":\"$zip_sha\",\"files_checked\":$checked,\"ts\":\"$ts\"}" >> "$AT"
echo "[assure] OK: $checked files verified; atlas stamped EXPORT_ZIP_ASSURED"
