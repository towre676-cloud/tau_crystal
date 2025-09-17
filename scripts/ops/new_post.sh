#!/usr/bin/env bash
set -euo pipefail
date="${1:-$(date +%Y-%m-%d)}"
title="${2:-tau-crystal-update}"
slug="$(echo "$title" | tr '[:upper:]' '[:lower:]' | sed 's/[^a-z0-9]+/-/g; s/[^a-z0-9-]//g; s/--*/-/g; s/^-//; s/-$//')"
excerpt="${3:-Auto-post from commit / receipt.}"
ledger_link="${4:-.tau_ledger/chain/CHAIN}"
post="docs/_posts/${date}-${slug}.md"
mkdir -p "docs/_posts"
cat > "$post" <<EOF2
---
layout: post
title: "$title"
date: ${date}
---

${excerpt}

- Ledger: [${ledger_link}](${ledger_link})
EOF2
echo "[blog] wrote $post"
