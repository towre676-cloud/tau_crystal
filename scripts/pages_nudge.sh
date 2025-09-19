#!/usr/bin/env bash
set -euo pipefail
touch docs/.nojekyll
git add docs/.nojekyll || true
git commit -m "docs: nudge GitHub Pages" || true
git push || true
echo "Triggered a Pages rebuild."
