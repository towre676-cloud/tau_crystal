#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
REQ_GH=${REQ_GH:-1}
git rev-parse --is-inside-work-tree >/dev/null 2>&1 || { echo "[coin] not a git repo"; exit 2; }
COMMIT=$(git rev-parse --verify HEAD)
SHORT=$(git rev-parse --short=12 HEAD)
TREE=$(git rev-parse HEAD^{tree})
STAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
OWNER=""; REPO=""; ORI=$(git config --get remote.origin.url || echo "")
case "$ORI" in
  git@github.com:*) O=$(printf "%s\n" "$ORI" | sed -E 's#^git@github.com:([^/]+)/([^\\.]+)(\\.git)?$#\1 \2#');;
  https://github.com/*) O=$(printf "%s\n" "$ORI" | sed -E 's#^https://github.com/([^/]+)/([^\\.]+)(\\.git)?$#\1 \2#');;
  *) O=" ";;
esac
OWNER=$(printf "%s\n" "$O" | awk "{print \$1}")
REPO=$(printf "%s\n" "$O" | awk "{print \$2}")
[ -n "$OWNER" ] && [ -n "$REPO" ] || { echo "[coin] cannot parse origin $ORI"; exit 3; }
TAG="export-repo-$SHORT"
Z="_exports/${REPO}-${SHORT}.zip"
R=".tau_ledger/exports/export_repo_${SHORT}.json"
git archive --format=zip --prefix="${REPO}/" -o "$Z" "$COMMIT"
BYTES=$(wc -c < "$Z" | tr -d " ")
if command -v sha256sum >/dev/null 2>&1; then SHAZ=$(sha256sum "$Z" | cut -d" " -f1); else SHAZ=$(shasum -a 256 "$Z" | cut -d" " -f1); fi
: > "$R"
printf "%s\n" "{" >> "$R"
printf "%s\n" "  \"schema\":\"taucrystal/export/v1\"," >> "$R"
printf "%s\n" "  \"kind\":\"repo_zip\"," >> "$R"
printf "%s\n" "  \"git_commit\":\"$COMMIT\"," >> "$R"
printf "%s\n" "  \"tree_sha\":\"$TREE\"," >> "$R"
printf "%s\n" "  \"zip_sha256\":\"$SHAZ\"," >> "$R"
printf "%s\n" "  \"zip_bytes\":$BYTES," >> "$R"
printf "%s\n" "  \"ts\":\"$STAMP\"" >> "$R"
printf "%s\n" "}" >> "$R"
AT="analysis/atlas.jsonl"; touch "$AT"
printf "%s\n" "{\"type\":\"EXPORT_ZIP\",\"git_commit\":\"$COMMIT\",\"zip_sha256\":\"$SHAZ\",\"bytes\":$BYTES,\"ts\":\"$STAMP\"}" >> "$AT"
if [ "$REQ_GH" = "1" ]; then
  command -v gh >/dev/null 2>&1 || { echo "[coin] gh not found; minted locally at $Z and $R"; exit 0; }
  if ! gh release view "$TAG" >/dev/null 2>&1; then gh release create "$TAG" -t "τ-Crystal Repo Export $TAG" -n "Deterministic repo ZIP + receipt for $COMMIT."; fi
  gh release upload "$TAG" "$Z" "$R" --clobber >/dev/null
  BASE="https://github.com/$OWNER/$REPO/releases/download/$TAG"
  URL_Z="$BASE/$(basename "$Z")"
  URL_R="$BASE/$(basename "$R")"
  sed -i.bak -E "s#\\{\"type\":\"EXPORT_ZIP\".*\\}$#{\"type\":\"EXPORT_ZIP\",\"git_commit\":\"$COMMIT\",\"zip_sha256\":\"$SHAZ\",\"bytes\":$BYTES,\"url\":\"$URL_Z\",\"receipt_url\":\"$URL_R\",\"ts\":\"$STAMP\"}#g" "$AT" 2>/dev/null || true
  MSG="Download $URL_Z ; compute sha256 and require $SHAZ ; abort if mismatch ; if match unzip and use folder ${REPO}/ exactly ; verify receipt at $URL_R shows zip_sha256=$SHAZ and git_commit=$COMMIT ; operate only on this archive and make no external fetches."
  echo "$MSG" > "_exports/llm_message_${SHORT}.txt"
  printf "%s\n" "[coin] published: $URL_Z" >&2
  printf "%s\n" "[coin] receipt:    $URL_R" >&2
  printf "%s\n" "[coin] one-line LLM message:" >&2
  printf "%s\n" "$MSG"
else
  echo "[coin] minted locally: $Z"; echo "[coin] receipt: $R"
fi
