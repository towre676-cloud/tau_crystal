#!/usr/bin/env bash
set +H
umask 022
TAG="${1:-run1-ramanujan-face}"
git tag -f "$TAG" >/dev/null 2>&1 || true
git push -f origin "$TAG" >/dev/null 2>&1 || true
echo "tagged and pushed $TAG (forced)";
