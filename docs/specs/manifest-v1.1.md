# τ-Crystal Manifest & Receipt Specification — v1.1

This document is the source of truth for manifests (tau-crystal-manifest.json) and receipts (tau-crystal-receipt.json). All field names and procedures below are normative.

## Objects

### Manifest (tau-crystal-manifest.json)
- kind (string) — literal "tau-crystal-manifest".
- version (string) — semantic schema version, here "1.1".
- timestamp_utc (string) — UTC ISO-8601, YYYY-MM-DDTHH:MM:SSZ.
- included_files (array) — each { "path": <posix>, "sha256": <hex64> }.
- archives (array) — each { "path": <posix>, "sha256": <hex64>, "alg": "tar.gz"|"zip" }.
- merkle_root (string) — hex64, computed as described below.
- prev_merkle_root (string, optional) — hex64 from previous commit’s manifest.
- signatures (array, optional) — detached references:  
  { "signer": <id>, "pubkey": <posix>, "signature": <posix>, "algo": "sha256-rsa/ecdsa" }.
- anchors (array, optional) — external proofs:  
  { "type": "ots", "path": <posix>, "sha256": <hex64> }.
- pow (object, optional) — { "bits": <int>, "nonce": <string> }.
- author|description|tags|source (optional metadata).

### Receipt (tau-crystal-receipt.json)
- kind (string) — literal "tau-crystal-receipt".
- version (string) — "1.1".
- timestamp_utc (string) — mirrors manifest timestamp.
- reflective (object) — mirror of verification surface:
  - merkle_root (string) — must equal manifest’s merkle_root.
  - files (array) — same entries as included_files.
  - archives (array) — same entries as archives.
  - signatures|anchors (optional) — mirrors if present.

## Deterministic inputs

All path values are POSIX-style with /. File lists are sorted lexicographically before hashing and packaging. JSON is serialized UTF-8 with 2-space indent and trailing newline. Timestamps are UTC Zulu and second-precision. Compression uses GNU tar format and ZIP_DEFLATED.

## Hashing

sha256(file) = hex digest of file bytes. Archive digests are over the produced .tar.gz and .zip bytes respectively.

## Merkle root

Let L = sort( [ sha256(f_i) for each included file ] ). While len(L) > 1, replace adjacent pairs by sha256( bytes.fromhex(a+b) ), duplicating the last element when the layer length is odd. The final element is merkle_root (hex64).

## Signature message

Detached signatures verify the message:
merkle_root + "\n" + timestamp_utc

Verification counts both attempted and successful validations. Threshold policies are enforced by CI configuration, not the schema.

## Proof of Work

When enabled, produce a nonce such that:
sha256( merkle_root + "|" + timestamp_utc + "|" + nonce )

has at least pow.bits leading zero bits. The message construction is normative.

## Chain continuity

prev_merkle_root must equal the previous commit’s merkle_root. CI MUST fetch depth ≥2 and verify link equality across commits.

## External anchoring

anchors[].type="ots" records an OpenTimestamps proof file placed next to the manifest. The anchor object’s sha256 is over the .ots file bytes.

## Archive determinism

Tar entries use relative POSIX paths, sorted, GNU format. Zip entries use POSIX paths, sorted, ZIP_DEFLATED. No extended attributes, no platform-specific metadata. Given identical inputs, the archives are byte-for-byte identical across OS.
