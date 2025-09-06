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
- **Merkle root:** 1c11d3ecac0beac2b80fd546e112ba7be7abe2781372665db91684f63270928f
- **Manifest timestamp (UTC):** 2025-09-06T17:15:22Z
- **docs/monographs.tar.gz (SHA-256):** 6571442532c1613c152aa5122c0ff267e8754d79bccf4bcc66c9cae32e5d3916
- **docs/monographs.zip (SHA-256):** d71ec8d0463701b7d1aae60517fb30bba8ac8b89106adf4689b6d6d72a9304d9
Files: [`tau-crystal-manifest.json`](tau-crystal-manifest.json), [`tau-crystal-receipt.json`](tau-crystal-receipt.json)
<!-- GOLDEN-OUTPUTS-END -->
