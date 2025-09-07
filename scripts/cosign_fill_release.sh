#!/usr/bin/env bash
set -euo pipefail
ROOT="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }
fail(){ printf "[FAIL] %s\n" "$1" >&2; exit 1; }
note(){ printf "[cosign] %s\n" "$1" >&2; }
ownrepo(){ r=$(git config --get remote.origin.url | sed -E 's#git@github.com:#https://github.com/#; s#\.git$##'); echo "$r" | sed -E 's#https://github.com/([^/]+)/([^/]+).*#\1 \2#'; }
read -r OWNER REPO <<<"$(ownrepo)"; OWNER="${OWNER:-towre676-cloud}"; REPO="${REPO:-tau_crystal}"
TAG="${1:-}"
if [ -z "$TAG" ]; then if git describe --tags --exact-match >/dev/null 2>&1; then TAG="$(git describe --tags --exact-match)"; else TAG="$(git tag --sort=-creatordate | head -n1)"; fi; fi
[ -n "$TAG" ] || fail "no git tags found; pass one explicitly: scripts/cosign_fill_release.sh v0.1.0"
FILE="${FILE:-}"
if [ -z "$FILE" ]; then
  cand=( "dist/tau_crystal-$TAG.tgz" "dist/tau-crystal-$TAG.tgz" "dist/tau_crystal-$TAG.tar.gz" "dist/tau-crystal-$TAG.tar.gz" "tau_crystal-$TAG.tgz" "tau-crystal-$TAG.tgz" "tau_crystal-$TAG.tar.gz" "tau-crystal-$TAG.tar.gz" )
  for f in "${cand[@]}"; do if [ -f "$f" ]; then FILE="$f"; break; fi; done
fi
[ -n "${FILE:-}" ] && [ -f "$FILE" ] || fail "release asset not found; set FILE=/path/to/asset (e.g., dist/tau_crystal-$TAG.tgz)"
SHA=$(sha256sum "$FILE" | awk "{print \$1}")
BLOB_SHA256="sha256:$SHA"
note "asset: $FILE"
note "blob sha256: $BLOB_SHA256"
README="README.md"; [ -f "$README" ] || : > "$README"
if grep -q "^## Verify this release (cosign)" "$README"; then
  tmp="$(mktemp)"
  awk -v tag="$TAG" -v file="$FILE" -v blob="$BLOB_SHA256" '
  BEGIN{in=0; seen=0}
  { line=$0
    if ($0 ~ /^## Verify this release \\(cosign\\)$/){seen=1}
    if (seen && $0 ~ /^```bash$/ && in==0){in=1; print; next}
    if (in==1 && $0 ~ /^```$/){in=0; print; next}
    if (in==1){
      if ($0 ~ /^TAG=/){print "TAG=" tag; next}
      if ($0 ~ /^FILE=/){print "FILE=" file; next}
      if ($0 ~ /^BLOB_SHA256=/){print "BLOB_SHA256=" blob; next}
      print
      next
    }
    print
  }
  ' "$README" > "$tmp" && mv "$tmp" "$README"
  if ! awk 'f{if($0~"^## Verify this release \\(cosign\\)$") s=1; if(s&&$0~/^```bash$/) b=1; else if(s&&$0~/^```$/&&b) {b=0; s=0} if(b&&$0~/^BLOB_SHA256=/) {print "yes"; exit}}' "$README" | grep -q yes; then
    tmp="$(mktemp)"
    awk -v blob="$BLOB_SHA256" '
    BEGIN{in=0; seen=0}
    {
      print
      if ($0 ~ /^## Verify this release \\(cosign\\)$/) seen=1
      if (seen && $0 ~ /^```bash$/ && in==0){in=1; print "BLOB_SHA256=" blob}
      if (in==1 && $0 ~ /^```$/){in=0}
    }
    ' "$README" > "$tmp" && mv "$tmp" "$README"
  fi
else
  note "README lacks cosign section; nothing to update"
fi
if [ -f docs/index.html ] && grep -q "Verify this release (cosign)" docs/index.html; then
  tmp="$(mktemp)"
  awk -v tag="$TAG" -v file="$FILE" -v blob="$BLOB_SHA256" '
  BEGIN{in=0}
  {
    if ($0 ~ /<pre><code>/) in=1
    if (in==1 && $0 ~ /^TAG=/){print "TAG=" tag; next}
    if (in==1 && $0 ~ /^FILE=/){print "FILE=" file; next}
    if (in==1 && $0 ~ /^BLOB_SHA256=/){print "BLOB_SHA256=" blob; next}
    if (in==1 && $0 ~ /<\/code><\/pre>/) in=0
    print
  }
  ' docs/index.html > "$tmp" && mv "$tmp" docs/index.html
fi
echo "[cosign] blob verify example:"
echo "cosign verify-blob --certificate \"$FILE.cert\" --signature \"$FILE.sig\" \"$FILE\""
echo "[cosign] attestation example (image digest optional):"
echo "cosign verify-attestation --type cyclonedx --certificate-oidc-issuer 'https://token.actions.githubusercontent.com' \\"
echo "  --certificate-identity 'https://github.com/$OWNER/$REPO/.github/workflows/release.yml@refs/tags/$TAG' ghcr.io/$OWNER/$REPO@sha256:<image-digest>"
