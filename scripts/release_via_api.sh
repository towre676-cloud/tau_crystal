#!/usr/bin/env bash
set -euo pipefail
ROOT="$HOME/Desktop/tau_crystal/tau_crystal"; cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }
fail(){ printf "[FAIL] %s\n" "$1" >&2; exit 1; }
note(){ printf "[rel] %s\n" "$1" >&2; }
[ -n "${GITHUB_TOKEN:-}" ] || fail "set GITHUB_TOKEN with repo:write"
[ $# -ge 1 ] || fail "usage: scripts/release_via_api.sh vX.Y.Z [dist/tau_crystal-vX.Y.Z.tgz] [title] [body-append]"
TAG="$1"; shift || true
TARBALL="${1:-dist/tau_crystal-$TAG.tgz}"; shift || true
TITLE="${1:-tau_crystal $TAG}"; shift || true
BODY_EXTRA="${1:-}"
[ -s "$TARBALL" ] || fail "asset missing: $TARBALL"
ownrepo(){ r=$(git config --get remote.origin.url | sed -E "s#git@github.com:#https://github.com/#; s#\\.git$##"); echo "$r" | sed -E "s#https://github.com/([^/]+)/([^/]+).*#\\1 \\2#"; }
read -r OWNER REPO <<<"$(ownrepo)"; [ -n "$OWNER" ] && [ -n "$REPO" ] || fail "cannot resolve owner/repo"
API=https://api.github.com/repos/$OWNER/$REPO
HDR=(-H "Accept: application/vnd.github+json" -H "Authorization: Bearer $GITHUB_TOKEN" -H "X-GitHub-Api-Version: 2022-11-28")
uploads_base="https://uploads.github.com/repos/$OWNER/$REPO/releases"
bname(){ bn=$(basename -- "$1"); printf "%s" "$bn"; }
json_escape(){ sed -e 's/\\/\\\\/g' -e 's/"/\\"/g' -e ":a;N;$!ba;s/\n/\\n/g"; }
get_release_by_tag(){ curl -sS "${HDR[@]}" "$API/releases/tags/$TAG" || true; }
create_release(){ curl -sS -X POST "${HDR[@]}" "$API/releases" -d @"$1"; }
patch_release(){ curl -sS -X PATCH "${HDR[@]}" "$API/releases/$1" -d @"$2"; }
list_assets(){ curl -sS "${HDR[@]}" "$API/releases/$1/assets"; }
del_asset(){ curl -sS -X DELETE "${HDR[@]}" "$API/releases/assets/$1" >/dev/null; }
upload_asset(){ rid="$1"; file="$2"; name="$(bname "$file")"; ct="${3:-application/gzip}"; curl -sS -X POST -H "Content-Type: $ct" -H "Authorization: Bearer $GITHUB_TOKEN" -H "Accept: application/vnd.github+json" "$uploads_base/$rid/assets?name=$name" --data-binary @"$file"; }
SHA=$(sha256sum "$TARBALL" | cut -d" " -f1)
BASE=$(bname "$TARBALL")
COSIGN_LINES=""; if [ -s "$TARBALL.sig" ] && [ -s "$TARBALL.cert" ]; then COSIGN_LINES="\n\ncosign verify-blob --certificate $BASE.cert --signature $BASE.sig $BASE"; fi
BODY="### Checksums\n\n\`$BASE\`\nSHA256: $SHA$COSIGN_LINES"; [ -n "$BODY_EXTRA" ] && BODY="$BODY\n\n$BODY_EXTRA"
BODY_JSON=$(printf "%s" "$BODY" | json_escape)
resp="$(get_release_by_tag)"
RID=$(printf "%s" "$resp" | sed -n 's/.*"id":[[:space:]]*\([0-9]\+\).*/\1/p' | head -n1)
URL=$(printf "%s" "$resp" | sed -n 's/.*"html_url"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -n1)
if ! printf "%s" "$resp" | grep -q "\"tag_name\":[[:space:]]*\"$TAG\""; then
  note "creating release $TAG"
  tmp=$(mktemp); printf '{"tag_name":"%s","name":"%s","body":"%s","draft":false,"prerelease":false}' "$TAG" "$TITLE" "$BODY_JSON" >"$tmp"
  resp="$(create_release "$tmp")"; rm -f "$tmp"
  RID=$(printf "%s" "$resp" | sed -n 's/.*"id":[[:space:]]*\([0-9]\+\).*/\1/p' | head -n1)
  URL=$(printf "%s" "$resp" | sed -n 's/.*"html_url"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -n1)
  [ -n "$RID" ] || fail "failed to create release (check token scope/repo)"
else
  note "release exists; updating body + assets"
  tmp=$(mktemp); printf '{"name":"%s","body":"%s"}' "$TITLE" "$BODY_JSON" >"$tmp"; patch_release "$RID" "$tmp" >/dev/null; rm -f "$tmp"
fi
assets="$(list_assets "$RID")"
for f in "$TARBALL" "$TARBALL.sig" "$TARBALL.cert"; do
  [ -s "$f" ] || continue
  name=$(bname "$f")
  aid=$(printf "%s" "$assets" | awk -v n="$name" '$0 ~ "\"name\":[[:space:]]*\""n"\"" {f=1} f && $0 ~ "\"id\":[[:space:]]*[0-9]+" {match($0, /"id":[[:space:]]*([0-9]+)/, a); print a[1]; exit}')
  [ -n "$aid" ] && { note "deleting existing asset $name (#$aid)"; del_asset "$aid" || true; }
  ct="application/gzip"; case "$name" in *.sig) ct="application/octet-stream";; *.cert) ct="application/pkix-cert";; esac
  note "uploading $name" ; upload_asset "$RID" "$f" "$ct" >/dev/null
done
README_UPDATE="${README_UPDATE:-1}"
if [ "$README_UPDATE" -eq 1 ]; then
  readme="README.md"; [ -f "$readme" ] || : > "$readme"
  hdr="## Verify this release ($TAG)"
  if ! grep -q "^$hdr\$" "$readme" 2>/dev/null; then
    tmp=$(mktemp)
    echo "$hdr" >>"$tmp"
    echo "" >>"$tmp"
    echo "```bash" >>"$tmp"
    echo "# fetch assets" >>"$tmp"
    echo "curl -sSLo \"$BASE\"       \"https://github.com/$OWNER/$REPO/releases/download/$TAG/$BASE\"" >>"$tmp"
    echo "[ -s \"$BASE.sig\" ]  || curl -sSLo \"$BASE.sig\"  \"https://github.com/$OWNER/$REPO/releases/download/$TAG/$BASE.sig\"" >>"$tmp"
    echo "[ -s \"$BASE.cert\" ] || curl -sSLo \"$BASE.cert\" \"https://github.com/$OWNER/$REPO/releases/download/$TAG/$BASE.cert\"" >>"$tmp"
    echo "" >>"$tmp"
    echo "# checksum (expected) — PASS prints \x27$BASE: OK\x27" >>"$tmp"
    echo "echo \"$SHA  $BASE\" | sha256sum -c -" >>"$tmp"
    echo "" >>"$tmp"
    echo "# (optional) cosign signature check" >>"$tmp"
    echo "cosign verify-blob --certificate \"$BASE.cert\" --signature \"$BASE.sig\" \"$BASE\"" >>"$tmp"
    echo "```" >>"$tmp"
    # insert after Quickstart if present; else append
    if grep -q "^## Quickstart\$" "$readme"; then
      out=$(mktemp); awk -v F="$tmp" '{print} /^## Quickstart$/ && !a {print ""; while ((getline l < F) > 0) print l; close(F); a=1}' "$readme" >"$out" && mv "$out" "$readme"
    else
      echo "" >>"$readme"; cat "$tmp" >>"$readme"
    fi
    rm -f "$tmp"
    note "README: inserted verify block for $TAG"
  else
    note "README: verify block already present for $TAG (skipped)"
  fi
fi
note "done → $URL"
