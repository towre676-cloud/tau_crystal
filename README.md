# τ‑Crystal Capsule Demonstration — demo_capsule_20250924T140554Z

This repository includes a live, downloadable, verifiable capsule containing a real payload, a signed receipt, a UTC timestamp, a notarization-ready affidavit, and verifier instructions. All components are portable, offline, cryptographically sealed, and legible under evidentiary rules including FRE 902(13), eIDAS, and PIPEDA.

Capsule location: analysis/capsules/demo_capsule_20250924T140554Z/demo_capsule_20250924T140554Z.zip
Receipt: analysis/capsules/demo_capsule_20250924T140554Z/receipt.json
Signature: analysis/capsules/demo_capsule_20250924T140554Z/receipt.sig
Affidavit (text): analysis/capsules/demo_capsule_20250924T140554Z/demo_capsule_20250924T140554Z_affidavit.txt
Bundle ZIP for direct distribution: analysis/publish/demo_capsule_20250924T140554Z_bundle.zip
SHA-256 for payload: analysis/capsules/demo_capsule_20250924T140554Z/demo_capsule_20250924T140554Z.zip.sha256
Public key to verify: analysis/capsules/demo_capsule_20250924T140554Z/pubkey.pem
Command-line verifier instructions: analysis/capsules/demo_capsule_20250924T140554Z/VERIFY.txt

To verify the authenticity of this capsule on any standard system:

Linux or macOS:
    sha256sum demo_capsule_20250924T140554Z.zip
    openssl dgst -sha256 -verify pubkey.pem -signature receipt.sig receipt.json

Windows (PowerShell or CMD):
    certutil -hashfile demo_capsule_20250924T140554Z.zip SHA256
    openssl dgst -sha256 -verify pubkey.pem -signature receipt.sig receipt.json

This capsule is complete and self-contained. The receipt and signature verify the contents. The notarization draft anchors the capsule in human legal time. The bundle ZIP contains all required elements for external parties to verify delivery integrity.

[![freed receipts (matrix)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-receipts-matrix.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-receipts-matrix.yml)


[![freed lab (all)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-lab.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-lab.yml)

[![freed TMF mock](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-tmf.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-tmf.yml)

[![freed eta-term report](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-eta.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-eta.yml)


[![freed angles (receipts set)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-angles.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/freed-angles.yml)

