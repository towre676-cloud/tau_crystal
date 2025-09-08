#!/usr/bin/env bash
set -euo pipefail
[ -n "${GITHUB_TOKEN:-}" ] || { echo "[FAIL] set GITHUB_TOKEN"; exit 1; }
R=$(git config --get remote.origin.url | sed -E "s#git@github.com:#https://github.com/#; s#\\.git$##")
OWNER=$(echo "$R" | sed -E "s#https://github.com/([^/]+)/([^/]+).*#\\1#")
REPO=$(echo "$R" | sed -E "s#https://github.com/([^/]+)/([^/]+).*#\\2#")
DESC="τ-Crystal: proof-carrying runtime manifest (receipts, CHAIN head, MERKLE_ROOT). Bash-only CI + signed releases."
HOMEPAGE="https://$OWNER.github.io/$REPO/"
API="https://api.github.com/repos/$OWNER/$REPO"
body=$(printf '{"description":"%s","homepage":"%s","has_issues":true,"has_wiki":false,"has_projects":false}' "$DESC" "$HOMEPAGE")
resp=$(mktemp); code=$(curl -sS -o "$resp" -w "%{http_code}" -X PATCH "$API" \
  -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github+json" -H "X-GitHub-Api-Version: 2022-11-28" \
  -d "$body")
if [ "$code" != "200" ]; then echo "[FAIL] PATCH /repos ($code)"; cat "$resp"; exit 1; fi
rm -f "$resp"
topics='{"names":["reproducibility","attestation","formal-verification","lean4","bash","receipt-chain","merkle-root","sigstore"]}'
code=$(curl -sS -o /dev/null -w "%{http_code}" -X PUT "$API/topics" \
  -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github+json" -H "X-GitHub-Api-Version: 2022-11-28" \
  -d "$topics")
if [ "$code" != "200" ]; then echo "[WARN] PUT /topics ($code)"; else echo "[ok] updated topics"; fi
echo "[ok] updated repo: $OWNER/$REPO" && echo "[ok] homepage: $HOMEPAGE"
