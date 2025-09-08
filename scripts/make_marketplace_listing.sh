#!/usr/bin/env bash
set -euo pipefail
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
OWNER_REPO=$(git config --get remote.origin.url | sed -E "s#git@github.com:#https://github.com/#; s#\.git\$##"); HOMEPAGE=$(echo "$OWNER_REPO" | sed -E "s#https://github.com/([^/]+)/([^/]+).*#https://\1.github.io/\2/#")
: > docs/marketplace-listing.md
add(){ printf "%s\n" "$1" >> docs/marketplace-listing.md; }
add "# τ-Crystal — Proof-carrying runtime manifest"
add ""
add "Turn your repo into a self-verifying system. τ-Crystal emits receipt chains, stamps a MERKLE_ROOT over tracked files, and provides copy-paste verification for releases and commits. Bash-only, CI-first, with signed release artifacts and SBOM support. Free for public repos; Pro for org-wide enforcement."
add ""
add "## Screenshots"
add "![](../media/shot-verify.png)"
add "![](../media/shot-ledger.png)"
add "![](../media/shot-soliton.png)"
add ""
add "## Key features"
add "- Receipt chain (CHAIN head ↔ receipt ↔ manifest)"
add "- MERKLE_ROOT over tracked files, status line in docs/manifest.md"
add "- Copy-paste release verification (sha256 + cosign verify-blob)"
add "- SBOM/attestation ready; bash-only CI; Pages mirror"
add ""
add "## Pricing"
add "**Free** — best for a team or two proving value."
add "**Pro — \$12,000/year** — organization-wide SSO/policy, required proof gates, higher CI throughput (10×), 180-day retention, diagnostics, priority support."
add ""
add "## Data & security"
add "- Manifests live in your repo; verifier artifacts retained per plan (14d Free, 180d Pro)."
add "- Signed releases recommended (cosign); SBOM (CycloneDX) optional."
add ""
add "## Links & support"
