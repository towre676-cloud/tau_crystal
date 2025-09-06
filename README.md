![Release](https://img.shields.io/github/v/release/towre676-cloud/tau_crystal?include_prereleases&sort=semver)

# tau_crystal
📄 [τ‑Crystal Monograph](docs/monographs/τ-crystal-monograph.md)

🪞 [τ‑Crystal Monograph Reflection](docs/monographs/τ-crystal-monograph-reflection.md)

📜 [τ‑Crystal Upgrade Monograph](docs/monographs/τ-crystal-upgrade.md)

[τ‑Crystal Upgrade Monograph](docs/monographs/tau-crystal-upgrade.md)

[tau-crystal-monograph-reflection.md](docs/monographs/tau-crystal-monograph-reflection.md)
[tau-crystal-monograph.md](docs/monographs/tau-crystal-monograph.md)
[tau-crystal-upgrade.md](docs/monographs/tau-crystal-upgrade.md)

## Spec & CLI

Start here: [Manifest Spec v1.1](docs/specs/manifest-v1.1.md) · [tauc CLI](scripts/tauc.py)

Quick start: `python scripts/tauc.py stamp` creates a fresh manifest and receipt from docs/monographs.

## Golden Outputs

Canonical examples live in [docs/golden](docs/golden). Merkle root shown inline for fast review.

## Verify release (Sigstore keyless)
```bash
# Download these from the GitHub Release assets for the tag you care about:
#   - dist/SHA256SUMS.txt
#   - dist/SHA256SUMS.txt.sig
#   - dist/SHA256SUMS.txt.pem  (certificate)
cosign verify-blob \
  --certificate dist/SHA256SUMS.txt.pem \
  --signature   dist/SHA256SUMS.txt.sig \
  --certificate-identity-regexp 'https://github.com/.*/.*/.github/workflows/release.yml@refs/tags/.*' \
  --certificate-oidc-issuer https://token.actions.githubusercontent.com \
  dist/SHA256SUMS.txt


τ-Crystal Synthesis Monograph (Formal Verification & Reproducibility)

<!-- GOLDEN-OUTPUTS-BEGIN -->
### Golden outputs
- **Merkle root:** 198235b501b83be3b7c4d490e74590e471126604ddae2a7a3c7a37e12af802b2
- **Manifest timestamp (UTC):** 2025-09-06T19:31:28Z
- **docs/monographs.tar.gz (SHA-256):** c0808b650dbd96ae08de6bfc7cdc1c97640916b3c22e225038ff46cde7301d6b
- **docs/monographs.zip (SHA-256):** 3285120b77c84fc596f6aac6ebc9a3bfa8e50d740cb5f6d9c99309840ac6830a
Files: [`tau-crystal-manifest.json`](tau-crystal-manifest.json), [`tau-crystal-receipt.json`](tau-crystal-receipt.json)
<!-- GOLDEN-OUTPUTS-END -->
