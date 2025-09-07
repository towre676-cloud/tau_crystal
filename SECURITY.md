# Security Policy

## Supported Versions
- The `main` branch is supported.
- Pro customers may receive advance patch notifications.

## Reporting Vulnerabilities
Please use GitHub private advisories or contact:
- Email: security@tau-crystal.example  *(placeholder)*
- Expected response: within **1 business day**
- Fix window: within **30 days** for critical issues

## Disclosure Policy
- We support coordinated disclosure.
- Reporters will be publicly credited unless anonymity is requested.

## Integrity Model
- `.tau_ledger/` contains all receipts and a hash‑linked `CHAIN`
- `docs/manifest.md` contains the `MERKLE_ROOT` and stamped `STATUS:`
- `attestation.txt` gives a signed human summary for audits
- All receipts are SHA‑256 verifiable and backed by a CI‑enforced gate
