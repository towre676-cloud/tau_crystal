#!/usr/bin/env bash
set -Eeuo pipefail; set +H
f="lake-manifest.json"; [ -s "$f" ] || { echo "unknown"; exit 0; }
rev=$(grep -A3 -E "\"name\"[[:space:]]*:[[:space:]]*\"mathlib\"" "$f" 2>/dev/null | grep -E "\"rev\"[[:space:]]*:" | head -n1 | sed -E "s/.*\"rev\"[[:space:]]*:[[:space:]]*\"([^\"]+)\".*/\1/")
[ -n "${rev:-}" ] && echo "$rev" || echo "unknown"
