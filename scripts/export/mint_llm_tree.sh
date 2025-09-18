#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
IDX="${1:-docs/llm_index.v1.json}"
[ -s "$IDX" ] || { echo "[tree] no index at $IDX"; exit 2; }
REPO_FULL=$(sed -n 's/.*"repo"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$IDX" | head -n1)
COMMIT=$(sed -n 's/.*"git_commit"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$IDX" | head -n1)
TAG=$(sed -n 's/.*"release_tag"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$IDX" | head -n1)
[ -n "$REPO_FULL" ] && [ -n "$COMMIT" ] || { echo "[tree] missing repo/commit"; exit 3; }
OWNER="${REPO_FULL%%/*}"; REPO="${REPO_FULL#*/}"
RAW_ROOT="https://raw.githubusercontent.com/$OWNER/$REPO/$COMMIT/"
OUT="docs/llm_tree.v1.jsonl"; : > "$OUT"
count=0
git -c core.autocrlf=false ls-tree -r --name-only -z "$COMMIT" | while IFS= read -r -d "" p; do
  [ -z "$p" ] && continue
  # compute sha256 and size from the committed blob
  if command -v sha256sum >/dev/null 2>&1; then S=$(git show "$COMMIT:$p" | sha256sum | cut -d" " -f1); else S=$(git show "$COMMIT:$p" | shasum -a 256 | cut -d" " -f1); fi
  B=$(git show "$COMMIT:$p" | wc -c | tr -d " ")
  printf "%s\n" "{\"path\":\"$p\",\"sha256\":\"$S\",\"bytes\":$B,\"raw_url\":\"${RAW_ROOT}${p}\"}" >> "$OUT"
  count=$((count+1))
done
echo "[tree] wrote $OUT with $count files"
COLOAD=""; [ -n "$TAG" ] && COLOAD="https://codeload.github.com/$REPO_FULL/zip/refs/tags/$TAG" || true
TMP="_tmp/llm_index.new.json"; : > "$TMP"
zip_url=$(sed -n 's/.*"zip_url"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$IDX" | head -n1)
zip_sha=$(sed -n 's/.*"zip_sha256"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$IDX" | head -n1)
zip_sha_url=$(sed -n 's/.*"zip_sha256_url"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$IDX" | head -n1)
receipt_url=$(sed -n 's/.*"receipt_url"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$IDX" | head -n1)
TREE_URL="https://raw.githubusercontent.com/$OWNER/$REPO/$COMMIT/docs/llm_tree.v1.jsonl"
{
  printf "%s\n" "{"
  printf "%s\n" "  \"version\": \"v1\","
  printf "%s\n" "  \"generated_utc\": \"$(date -u +"%Y-%m-%dT%H:%M:%SZ")\","
  printf "%s\n" "  \"repo\": \"$REPO_FULL\","
  printf "%s\n" "  \"git_commit\": \"$COMMIT\","
  printf "%s\n" "  \"tree_sha\": \"$(git rev-parse "$COMMIT^{tree}")\","
  printf "%s\n" "  \"release_tag\": \"${TAG}\","
  printf "%s\n" "  \"zip_url\": \"${zip_url}\","
  printf "%s\n" "  \"zip_sha256\": \"${zip_sha}\","
  printf "%s\n" "  \"zip_sha256_url\": \"${zip_sha_url}\","
  printf "%s\n" "  \"codeload_zip_url\": \"${COLOAD}\","
  printf "%s\n" "  \"tree_index_url\": \"${TREE_URL}\","
  printf "%s\n" "  \"raw_root\": \"${RAW_ROOT}\","
  printf "%s\n" "  \"receipt_url\": \"${receipt_url}\""
  printf "%s\n" "}"
} > "$TMP"
mv "$TMP" "$IDX"
W="docs/.well-known/llm-first-pass.json"; : > "$W"
printf "%s\n" "{" >> "$W"
printf "%s\n" "  \"llm_start_here\": \"https://raw.githubusercontent.com/$OWNER/$REPO/main/LLM_START_HERE.txt\"," >> "$W"
printf "%s\n" "  \"llm_index\": \"https://raw.githubusercontent.com/$OWNER/$REPO/main/docs/llm_index.v1.json\"," >> "$W"
printf "%s\n" "  \"tree_index_url\": \"${TREE_URL}\"" >> "$W"
printf "%s\n" "}" >> "$W"
echo "[tree] updated llm_index and well-known pointer"
