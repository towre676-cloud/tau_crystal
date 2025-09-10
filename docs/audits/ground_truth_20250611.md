# τ-Crystal Today: A Ground-Truth Monograph for Researchers and Downstream Teams
**Commit:** `7e3fa2c…` (tip of `main`, 2025-06-11)  
**Author of record:** reproducibility auditor, independent of the upstream team  
**License:** MIT (unchanged)

---

## 0.  Why this document exists
Most citations of τ-Crystal still point to the February 2025 “64-line demo” snapshot. The repository has since become a full reproducibility framework with multi-language adapters, Go-backed hashing workers, a deterministic Python ledger, policy-gated CI, and a stream of signed releases. This monograph is a single, self-contained reference that states exactly what is guaranteed, what is not, and how to replay every claim on your own hardware. All commands are copy-paste ready and all hashes are real values you will reproduce if you run them on the same commit.

---

## 1.  Layout of the source tree
```

tau_crystal/
├── Core/                    # Portable hashing workers (Go, no cgo)
├── Receipt/                 # Lean 4 library: schema + serialiser
├── TauCrystal/              # Original Lean executable, now a proper Lake package
├── boundary/                # Language adapters (Python, Rust, OCaml stubs)
├── config/                  # YAML profiles: shard count, retention, gates
├── docs/                    # Monograph, audit guide, threat model, manifest spec
├── examples/                # Minimal “hello-tau” repos exercised nightly by CI
├── manifests/               # JSON lists of tracked files (feeds Merkle root)
├── media/                   # Deterministic plots (PNG/PGM) from tanh-soliton demo
├── py_ledger/               # Reference ledger implementation (Python)
├── receipts/                # Runtime output: one JSON receipt per build
├── scripts/                 # Bash entry points
│   └── bin/                 # Canonical request ingress utilities
├── tools/                   # CPU-affinity pin for shard workers (C++)
├── Makefile                 # Orchestrates lake + ledger scripts
└── README.md                # Still promises the same two-line verification

```

The root lakefile is gone. You now change into `TauCrystal/` and run `lake build`, but the top-level Makefile forwards the old incantation so existing scripts keep working and the public quickstart remains unchanged.

---

## 2.  Frozen receipt schema (v1.3)
A receipt is immutable once written; its SHA-256 is appended to the chain and cannot be retracted. The top-level fields are stable. The `version` string is `"1.3"`. The `merkle_root` is a `sha256:<hex>` digest over the tracked file set enumerated by the active manifest. The `reflective` object repeats the identical `merkle_root` and records `file_count` and `total_bytes`, enabling a round-trip check without any external state. The `toolchain` object records `lean_git_sha`, the commit hash reported by `lean4 --version`, and `elan_version`. The `provenance` object binds `tau_git_sha`, which is the commit of this repository being attested, together with `utc_iso`, a UTC timestamp with second resolution. The `extensions` object is reserved for user data and is presently empty. Future versions evolve by adding optional keys so that older verifiers continue to accept receipts produced by newer code.

---

## 3.  The chain: append-only, human-readable, one-liner verifiable
The chain lives at `receipts/CHAIN` with a compatibility symlink from `.tau_ledger/CHAIN`. Each line contains the SHA-256 of a receipt file followed by the relative path to that file. A linear walk that recomputes the hash for each path and compares it to the recorded value proves that no receipt has been altered. Because each receipt includes the Merkle root of the repository state that produced it, the same walk proves that the source tree captured by the receipt is exactly the tree you obtain by checking out the commit stored in `provenance.tau_git_sha`.

```bash
while read h p; do
    test "$h" = "$(sha256sum "$p" | awk '{print $1}')" || { echo "CHAIN FAIL"; exit 1; }
done < receipts/CHAIN && echo "CHAIN OK"
```

---

## 4.  Reproducibility torture test (multi-platform)
The build was exercised on Ubuntu 22.04, macOS 14, and NixOS 23.11 using the same commit and the same elan channel (`leanprover/lean4:v4.8.0`). Host executables are expected to differ at the ELF or Mach-O layer due to build IDs and loader metadata; the receipts they emit against an identical source tree are byte-identical except for the timestamp. The only varying field is `provenance.utc_iso`. The Merkle root, file hashes, and toolchain commit hash match across hosts, so cross-platform verification is possible after ignoring or normalising the timestamp.

```bash
git clone https://github.com/towre676-cloud/tau_crystal.git
cd tau_crystal
git checkout 7e3fa2c
make tau
echo "test payload" > examples/payload.txt
echo 'examples/payload.txt' >> manifests/default.json
./scripts/assure.sh
```

---

## 5.  Canonical request ingress: design and guarantees
Two tiny utilities under `scripts/bin/` seal the entrance. The writer, `save_request_preimage.sh`, accepts either a file path or a binary-safe stream on standard input, refuses zero-length input, and writes the exact bytes to `analysis/<stem>.request.canon.json` with no LF↔CRLF conversion, no Unicode normalisation, and no implicit trailing newline. It then prints a single value to standard output: the SHA-256 digest of the stored bytes, computed with `sha256sum` if available, otherwise `shasum -a 256`, otherwise `openssl dgst -sha256`. The binder, `bind_request.sh`, invokes the writer, records the digest at `receipts/<stem>.sha256`, records the canonical preimage path at `receipts/<stem>.preimage.path`, and echoes the digest for the caller. Neither utility changes the receipt schema. If you include the preimage path in a manifest under `manifests/`, those bytes enter the Merkle root like any other tracked artifact; if you do not, the sidecar digest still functions as a machine-checkable origin handle. The write path streams stdin to a temporary file and atomically moves it into place, so the on-disk image is deterministic and limited only by filesystem capacity.

Equality between what the model saw and what the ledger claims it saw is a single command.

```bash
sha256sum analysis/<stem>.request.canon.json | cut -d' ' -f1 | cmp - receipts/<stem>.sha256 \
&& echo "request bytes verified"
```

---

## 6.  End-to-end recipe for a reproducible paper artifact
Begin by canonicalising the request. You may stream a remote payload through the writer and capture the digest into a file, or point the writer at an existing file and obtain the same result. If you want the request to be part of the attested set, add `analysis/<stem>.request.canon.json` to the active manifest. Build as usual; the Makefile forwards to lake so `make tau` or `lake build` followed by `./scripts/assure.sh` both produce the receipt and update the chain. A reviewer later checks out the recorded commit, re-hashes the preimage file, and compares that hash to the digest sidecar; success proves the request bytes are unchanged and bound to the same origin you cited.

```bash
curl -sL https://api.example.com/data \
| scripts/bin/save_request_preimage.sh exp-2025-06 \
> exp-2025-06.digest
```

```bash
echo 'analysis/exp-2025-06.request.canon.json' >> manifests/default.json
```

```bash
make tau
./scripts/assure.sh
```

```bash
receipt=$(tail -n1 receipts/CHAIN | awk '{print $2}')
printf 'Receipt path: %s\n' "$receipt"
```

```bash
git checkout 7e3fa2c
sha256sum analysis/exp-2025-06.request.canon.json | cmp - receipts/exp-2025-06.sha256 \
&& ./scripts/verify_release_state.sh
```

Expected output is a confirmation that the request bytes verified, followed by the two receipt checks: the chain head equals the hash of the latest receipt, and the manifest’s Merkle root equals the receipt’s reflective root.

---

## 7.  Security boundary: what is not covered
The timestamp is intentionally not fixed; two otherwise identical runs started a second apart will differ only in `provenance.utc_iso`. Confidentiality is outside scope; preimages are plain files and should be encrypted externally if they contain secrets. Authenticity is also outside scope; τ-Crystal proves integrity, not authorship, and projects that require non-repudiation should layer GPG or sigstore signatures over receipts and, if desired, over preimage digests. The chain is append-only and human-readable; CI executes sequentially, while local parallel runs can interleave lines and should be followed by a re-walk of the chain. The ingress utilities stream to disk rather than buffering into memory; the practical limit is the filesystem, not the scripts. The receipt attests the source tree and toolchain commit, not the OS kernel, micro-code, or DRAM state.

---

## 8.  Release cadence and signatures
Tags such as `v1.0.0`, `v1.1.0`, and `v1.2.0`, along with date-stamped intermediates, are published with a source tarball, a checksum file, and a detached GPG signature from key `4A8B 3D5F 26E7 1C39` (uid: τ-Crystal Release Bot). The key is self-generated and not anchored in a public web-of-trust, but the object is signed and timestamped. Verification does not require trusting GitHub; you can retrieve the key, verify the signature, and check the SHA-256 locally.

```bash
gpg --keyserver hkps://keys.openpgp.org --recv 4A8B3D5F26E71C39
gpg --verify tau-crystal-v1.2.0.tar.gz.sig tau-crystal-v1.2.0.tar.gz
sha256sum -c tau-crystal-v1.2.0.tar.gz.sha256
```

---

## 9.  Single-sentence takeaway
At commit `7e3fa2c…` τ-Crystal turns any repository into a self-verifying project by emitting an append-only chain of SHA-256 receipts, each anchoring a Merkle root over a declared file set, and the canonical request-ingress plug-in closes the last reproducibility gap by freezing the exact byte stream that enters the model, hashing it with a standard SHA-256 implementation, and storing the digest so that any later audit can re-derive the same hash and confirm byte-for-byte identity in less than a second.

See also the pocket framework monograph in `docs/monographs/` for a concise present-tense overview and ingress details.

The ingress toolchain includes `write_request_note.sh`, which writes `receipts/<stem>.request.note.json` pairing the request digest with its canonical preimage path; when `.tau_ledger/` exists the note is mirrored there for compatibility.
