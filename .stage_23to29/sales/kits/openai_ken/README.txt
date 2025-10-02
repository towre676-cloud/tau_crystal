OpenAI — SecOps Toolchain Intake — Sealed Delivery Capsule (Starter)

Provenance-sealed tool/bundle with CI-verifiable signature; optional affidavit for external legal exchanges.

Contents you will place later:
  artifacts/your_bundle.zip            # the exact bytes you promise
  artifacts/your_bundle.zip.sha256     # sha256sum of the bundle
  docs/affidavit.pdf                   # notarized scan (optional now)
  ledger/receipt.json                  # signed receipt (you will sign)
  ledger/receipt.sig                   # signature over receipt.json
  ledger/affidavit.ledger.json         # notary metadata (fill after stamp)

Acceptance: delivery is complete when your SHA-256 and signature checks pass (see VERIFY.txt).
Support: if your computed hash differs, reply with your hex and we will reconcile.
