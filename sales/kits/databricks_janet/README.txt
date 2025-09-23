Databricks — Audit / GRC Export — Sealed Delivery Capsule (Starter)

Sealed dataset or logs export with hash+signature and optional affidavit for SOX/SOC evidence.

Contents you will place later:
  artifacts/your_bundle.zip            # the exact bytes you promise
  artifacts/your_bundle.zip.sha256     # sha256sum of the bundle
  docs/affidavit.pdf                   # notarized scan (optional now)
  ledger/receipt.json                  # signed receipt (you will sign)
  ledger/receipt.sig                   # signature over receipt.json
  ledger/affidavit.ledger.json         # notary metadata (fill after stamp)

Acceptance: delivery is complete when your SHA-256 and signature checks pass (see VERIFY.txt).
Support: if your computed hash differs, reply with your hex and we will reconcile.
