#!/usr/bin/env bash
set -euo pipefail
ROOT="$HOME/Desktop/tau_crystal/tau_crystal"
cd "$ROOT" || { echo "[err] bad root: $ROOT"; exit 1; }

# repo info
remote_url="$(git config --get remote.origin.url || true)"
repo_path="$(printf '%s\n' "$remote_url" | sed -E 's#(git@|https?://)github.com[:/](.+)(\.git)?#\2#')"
[ -n "$repo_path" ] || repo_path="$(basename "$(pwd)")"
plan="FREE"; [ -f ".tau_plan_roots.env" ] && plan="$(grep -E '^TAU_PLAN=' .tau_plan_roots.env | cut -d= -f2 || echo FREE)"

# README blocks
touch README.md
readme_badges="\
[![Plan: ${plan}](https://img.shields.io/badge/plan-${plan}-blue?style=flat-square)](./.tau_plan_roots.env)
[![CI](https://img.shields.io/github/actions/workflow/status/${repo_path}/verify.yml?style=flat-square)](https://github.com/${repo_path}/actions)
[![Attestation](https://img.shields.io/badge/attestation-ledger-green?style=flat-square)](./.tau_ledger/attestation.txt)
"
quickstart_block="## Quickstart

\`\`\`bash
# from repo root
bash scripts/plan/tau_pro_gate.sh
bash scripts/plan/write_roots.sh
TAU_MAX_SHARDS=\${TAU_MAX_SHARDS:-20} ./scripts/plan/launch_verifiers.sh
\`\`\`

- Latest status: see \`docs/manifest.md\` (STATUS + MERKLE_ROOT)
- Receipts: \`.tau_ledger/receipts/\`
- Chain head: \`.tau_ledger/CHAIN\`
- Human summary: \`.tau_ledger/attestation.txt\`
"

plans_block="## Plans

**τ‑Crystal** is free for public repos and small private experiments.  
**Pro** (\$12k/year) turns it into an org-grade verification spine:

- Organization-wide SSO and policy enforcement
- 10× CI throughput with formal proof gates required
- 180-day manifest retention, Merkle root stamping
- Receipt chain with immutable attestation export

If your auditors, insurers, or treasury depend on this, you want **Pro**.
"

links_block="## Docs

- **Manifest spec**: \`docs/specs/manifest-v1.1.md\` (if present)
- **Live manifest**: \`docs/manifest.md\`
- **Ledger attestation**: \`.tau_ledger/attestation.txt\`
- **Audit guide**: \`docs/AUDIT.md\`
- **CI notes**: \`docs/ci.md\`
"
# README updates (idempotent)
if ! grep -q 'Plan:' README.md 2>/dev/null; then
  tmp="$(mktemp)"; { printf '%s\n\n' "$readme_badges"; cat README.md; } > "$tmp" && mv "$tmp" README.md
fi
grep -q '^## Quickstart' README.md 2>/dev/null || printf '\n%s\n' "$quickstart_block" >> README.md
grep -q '^## Plans' README.md 2>/dev/null     || printf '\n%s\n' "$plans_block"     >> README.md
grep -q '^## Docs' README.md 2>/dev/null      || printf '\n%s\n' "$links_block"     >> README.md

# tiny architecture diagram
mkdir -p docs
if [ ! -f docs/diagram-architecture.svg ]; then
cat > docs/diagram-architecture.svg <<'SVG'
<svg xmlns="http://www.w3.org/2000/svg" width="720" height="360">
  <rect width="100%" height="100%" fill="#0b0f1a"/>
  <g font-family="monospace" font-size="12" fill="#e6edf3">
    <rect x="40" y="40" width="180" height="80" rx="10" fill="#1f2a44" stroke="#4b6fa9"/>
    <text x="50" y="70">Repo</text><text x="50" y="90">git ls-files → MERKLE_ROOT</text>
    <rect x="260" y="40" width="200" height="80" rx="10" fill="#1f2a44" stroke="#4b6fa9"/>
    <text x="270" y="70">Plan Gate</text><text x="270" y="90">TAU_* flags</text>
    <rect x="500" y="40" width="180" height="80" rx="10" fill="#1f2a44" stroke="#4b6fa9"/>
    <text x="510" y="70">Launcher</text><text x="510" y="90">proof gate + workers</text>
    <rect x="140" y="170" width="220" height="80" rx="10" fill="#1f2a44" stroke="#4b6fa9"/>
    <text x="150" y="200">Receipt</text><text x="150" y="220">JSON + CHAIN</text>
    <rect x="420" y="170" width="220" height="80" rx="10" fill="#1f2a44" stroke="#4b6fa9"/>
    <text x="430" y="200">Manifest</text><text x="430" y="220">STATUS + ROOT</text>
    <line x1="220" y1="80" x2="260" y2="80" stroke="#7aa2f7"/>
    <line x1="460" y1="80" x2="500" y2="80" stroke="#7aa2f7"/>
    <line x1="300" y1="210" x2="420" y2="210" stroke="#7aa2f7"/>
    <line x1="150" y1="120" x2="250" y2="170" stroke="#7aa2f7"/>
    <line x1="570" y1="120" x2="530" y2="170" stroke="#7aa2f7"/>
  </g>
</svg>
SVG
fi

# CI notes
cat > docs/ci.md <<'MD'
# CI Notes
- Workflow: `.github/workflows/verify.yml` (launcher → receipt → manifest → attestation)
- Badges: README shows current CI and plan
- Matrix tip: set `fail-fast: false` for complete coverage
- Env flags: `TAU_PLAN`, `TAU_REQUIRE_PROOFS`, `TAU_MAX_WORKERS`, `TAU_RETENTION_DAYS`
MD
# Audit walk-through
cat > docs/AUDIT.md <<'MD'
# AUDIT — τ‑Crystal
## Verify MERKLE_ROOT matches repo state
git ls-files -z | xargs -0 sha256sum | LC_ALL=C sort -k2 > /tmp/list.txt
sha256sum /tmp/list.txt | awk '{print $1}'   # compare to docs/manifest.md

## Verify receipts and chain linkage
tail -n 5 .tau_ledger/CHAIN
sha256sum .tau_ledger/receipts/*.json | head

## Check receipt ↔ manifest root (jq optional)
jq -r '.merkle_root' tau-crystal-manifest.json
jq -r '.reflective.merkle_root' tau-crystal-receipt.json
MD

# Optional Pages landing
cat > docs/index.html <<'HTML'
<!doctype html><meta charset="utf-8"><title>τ‑Crystal — Attestation</title>
<style>body{font:16px/1.5 system-ui;background:#0b0f1a;color:#e6edf3;margin:40px}
a{color:#7aa2f7;text-decoration:none} .card{background:#111827;padding:16px;border-radius:12px;
box-shadow:0 0 0 1px #1f2a44 inset;margin-bottom:16px}</style>
<h1>τ‑Crystal</h1>
<div class="card"><p>See <a href="../README.md">README</a>, <a href="manifest.md">manifest</a>,
and <a href="../.tau_ledger/attestation.txt">attestation.txt</a>.</p>
<p><img src="diagram-architecture.svg" alt="diagram" width="560"></p></div>
HTML

# Repo tree snapshot
if command -v tree >/dev/null 2>&1; then tree -L 2 > docs/REPO_TREE.md
else { echo "# Repo Tree (2 levels)"; echo; find . -maxdepth 2 -type d -print | sort; } > docs/REPO_TREE.md; fi

# Commit if changed
git add README.md docs || true
if ! git diff --cached --quiet; then
  git commit -m "docs: badges, quickstart, audit guide, CI notes, diagram, repo tree" || true
fi
echo "[polish] done."
