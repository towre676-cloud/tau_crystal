# τ‑Crystal

τ‑Crystal is a Bash‑only harness for reproducible science and research verification. It runs a set of precise checks (called 'gates') across a repository, seals cryptographically verifiable bundles (called 'capsules'), and records a small, four‑column table showing which subsystems are passing.

Each run produces a signed receipt, a Merkle root, and a compact audit trail that survives across platforms and architectures. The system requires no Docker, no Python environment, and no internet access. Everything it produces can be re‑verified using Bash and coreutils alone.

### Getting Started

Clone the repo and run the hammer:

\```bash
cd tau_crystal
bash scripts/ops/next_hammer.sh
\```

If everything passes, you'll see a tidy table like this:

    organ        status    last_ok_utc             last_error
    phasehead    ok        2025‑09‑21T12:34:56Z     -
    ckm          ok        2025‑09‑21T12:34:56Z     -
    capsules     ok        2025‑09‑21T12:34:57Z     -

If something fails, the table will show which organ failed and why. The system does not hide drift — it signs and stores it.

### Repository Layout (Plain Words)

The first time you open this tree, you’ll see some unfamiliar folders. Here’s what they mean:

- `analysis/` is the result pile. TSVs, plots, receipts, summaries. Don’t edit this — it’s a record, not a source.
- `.tau_ledger/` is the cryptographic log. Every sealed run, every signed receipt, every Merkle root lands here.
- `scripts/ops/next_hammer.sh` is the entry point. This is the main command. It runs every gate in a fixed order.
- `scripts/gates/` are the small, focused checks (e.g., CKM matrix unitarity, boundary signatures, capsule hashing).
- `scripts/meta/` contains helpers that print the table, seal capsules, or update the ledger.

Capsules are created in `analysis/capsules/`. Each one includes a boundary.txt, its matching boundary.sig, and a capsule.receipt.json. These folders are portable, tamper‑evident, and can be replayed anywhere with Bash.

### Quick Ritual

To test that the system is wired correctly, run this from the repo root:

\```bash
bash scripts/ops/next_hammer.sh && bash scripts/meta/progress_print.sh
\```

You’ll see a full-status table. If you’re curious, open the latest capsule directory and inspect the receipt. If you’re not, the table is already your witness.

_Last updated: 2025-09-22T20:05:29Z UTC_
## Verify a Capsule (OpenSSL, no internet)
Requirements: `openssl`, `sha256sum`.

```bash
# 1) Check the hash
sha256sum auto-20250922T220241Z.tar.gz | awk '{print $1}' \
 | diff -u - auto-20250922T220241Z.tar.gz.sha256

# 2) Check the receipt hash matches
 | sed 's/.*ed25519_openssl://' | tr -d '\r' | openssl base64 -d -A > sig.bin

openssl pkeyutl -verify -pubin -inkey seller_ed25519.pub.pem -rawin \
  -sigfile sig.bin -in auto-20250922T220241Z.tar.gz && echo "Signature OK"
```
