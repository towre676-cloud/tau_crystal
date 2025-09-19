#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
echo "::group::Morpho publish + stamp + tag + release"
# 1) Ensure a stamped pack exists and print the canonical line
scripts/morpho/bridge_publish_wrapped.sh || true
PACK="$(ls -1dt analysis/morpho/packs/run_* 2>/dev/null | head -n1)"
[ -n "$PACK" ] && [ -d "$PACK" ] || { echo "no packs found" >&2; exit 2; }
scripts/morpho/after_publish.sh "$PACK" || exit 3

# 2) Derive canonical tag from ROOT and push it
REC="$PACK/corridor.receipt.tsv"; GLB="$PACK/global.L"
[ -f "$REC" ] && [ -f "$GLB" ] || { echo "missing receipt/global.L" >&2; exit 4; }
ROOT="$(awk '$1=="ROOT"{print $2}' "$REC" | head -n1)"
[ -n "$ROOT" ] || { echo "receipt missing ROOT" >&2; exit 5; }
TAG="morpho-pack-${ROOT:0:12}"
git tag -f "$TAG"
git push origin "refs/tags/$TAG" -f
echo "retagged: $TAG"

# 3) Compute human release title and create/edit the release
TITLE="$(scripts/morpho/release_name_from_receipt.sh "$PACK")"
[ -n "$TITLE" ] || { echo "empty release title" >&2; exit 6; }
if gh release view "$TAG" >/dev/null 2>&1; then
  gh release edit "$TAG" --title "$TITLE" >/dev/null
else
  gh release create "$TAG" --title "$TITLE" --generate-notes >/dev/null
fi
echo "::notice title=Release::${TITLE} (#${TAG})"
echo "::endgroup::"
