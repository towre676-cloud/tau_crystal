#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
echo "::group::Morpho publish + stamp + tag + release"
scripts/morpho/bridge_publish_wrapped.sh || true
PACK="$(scripts/morpho/latest_complete_pack.sh 2>/dev/null || true)"
[ -n "$PACK" ] && [ -d "$PACK" ] || { echo "no complete packs found"; echo "::endgroup::"; exit 0; }
scripts/morpho/after_publish.sh "$PACK" || exit 3
REC="$PACK/corridor.receipt.tsv"; GLB="$PACK/global.L"
[ -f "$REC" ] && [ -f "$GLB" ] || { echo "missing receipt/global.L"; echo "::endgroup::"; exit 0; }

# Geometry strict gate: soft by default; set HARD=1 to require pass
GATE_MODE="soft"; [ "${HARD:-0}" = "1" ] && GATE_MODE="hard"
scripts/morpho/geom_gate.sh "$GATE_MODE" "$PACK" || { echo "strict gate blocked release"; echo "::endgroup::"; exit 0; }

ROOT="$(awk '$1=="ROOT"{print $2}' "$REC" | head -n1)"
[ -n "$ROOT" ] || { echo "receipt missing ROOT"; echo "::endgroup::"; exit 0; }
TAG="morpho-pack-${ROOT:0:12}"
git tag -f "$TAG" >/dev/null
git push origin "refs/tags/$TAG" -f >/dev/null
TITLE="$(scripts/morpho/release_name_from_receipt.sh "$PACK")"
[ -n "$TITLE" ] || TITLE="Craniofacial Certificate — $TAG"
if gh release view "$TAG" >/dev/null 2>&1; then gh release edit "$TAG" --title "$TITLE" >/dev/null; else gh release create "$TAG" --title "$TITLE" --generate-notes >/dev/null; fi
echo "::notice title=Release::${TITLE} (#${TAG})"
echo "::endgroup::"
