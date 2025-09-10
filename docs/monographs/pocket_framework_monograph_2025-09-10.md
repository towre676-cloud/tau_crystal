# τ-Crystal: Pocket-Sized Framework — Current State

τ-Crystal now presents itself as a finished, pocket-sized framework rather than a proof-of-concept. At the root you find the customary Unix directories—Core, Receipt, TauCrystal, boundary, config, docs, examples, manifests, media, py_ledger, receipts, scripts (with its own bin/), tools—each containing only what is required and nothing more. The build is still Lake-based, but the Lakefile has moved inside TauCrystal/ where it compiles both the library and the receipt-emitting executable; a thin top-level Makefile exposes the familiar `make tau` target that produces the same native binary you run locally via `./scripts/assure.sh` and that CI invokes unchanged. There is no stub main, no hard-wired JSON payload, no toy theorems exported by fiat; the executable links the full TauCrystal library and writes a receipt whose contents are determined at runtime.

Ingress is handled by two scripts that refuse to guess. `save_request_preimage.sh` accepts either a named file or an arbitrary byte stream on stdin, rejects empty input, and stores the exact bytes—no added newline, no encoding massage, no fsync—at `analysis/<stem>.request.canon.json`. When reading from stdin it streams to a temporary file and renames it into place; when given a source file it copies byte-for-byte directly to the destination. Its only output is the SHA-256 of those bytes, printed to stdout **with a trailing newline**. `bind_request.sh` never moves the preimage; it simply records the digest in `receipts/<stem>.sha256`, writes the canonical preimage path to `receipts/<stem>.preimage.path`, and echoes the digest again for the caller. Because the data path is a straight copy to disk, memory usage is bounded by kernel page cache, not by the size of the request.

The verification contract published in the README remains the single ground truth. After every run the head of `receipts/CHAIN` must equal the SHA-256 of the receipt file it names, and the manifest’s `merkle_root` must equal the `reflective.merkle_root` field inside that same receipt. CI enforces exactly those two equalities; a local run can do the same with the one-line command printed at the end of `./scripts/assure.sh`. The ingress layer does not alter the schema—it only seals the final seam by guaranteeing that the request bytes seen by the computation are the same bytes whose hash enters the ledger. If you list `analysis/<stem>.request.canon.json` among the tracked files, its digest becomes part of the Merkle root; if you leave it out, the sidecar digest in `receipts/` still provides an immutable, machine-checkable handle to the original request. In short, τ-Crystal is now a small, complete receipt framework: an append-only chain under `receipts/`, a Lake-driven build wrapped by a Makefile, and a streaming ingress that canonizes request bytes before they ever reach the computation.

In environments that still expect the legacy layout, the binder also mirrors the sidecar files to `.tau_ledger/` when that directory exists. This keeps older audit tools working while the canonical location remains `receipts/`.

For human-friendly provenance, `scripts/bin/write_request_note.sh` emits a tiny JSON note that pairs the request digest with its canonical preimage path. The file lives at `receipts/<stem>.request.note.json` (and is mirrored under `.tau_ledger/` when present) and looks like `{"request_sha256":"…","preimage_path":"analysis/<stem>.request.canon.json"}`.

## Golden diff: fast drift check

A one-character change advances the chain head exactly as advertised. This sequence is safe and reversible:

```bash
base=$(tail -n1 receipts/CHAIN | awk '{print $1}')
printf " " >> README.md
make tau && ./scripts/assure.sh
head=$(tail -n1 receipts/CHAIN | awk '{print $1}')
[ "$base" = "$head" ] && echo "FAIL – no diff" || echo "PASS – diff: $base -> $head"
git checkout -- README.md
```

For a host-agnostic, replayable audit narrative, see the ground-truth audit under `docs/audits/`.

In environments that still expect the legacy layout, the binder also mirrors the sidecar files to `.tau_ledger/` when that directory exists. This keeps older audit tools working while the canonical location remains `receipts/`.

For human-friendly provenance, `scripts/bin/write_request_note.sh` emits a tiny JSON note that pairs the request digest with its canonical preimage path at `receipts/<stem>.request.note.json` (mirrored under `.tau_ledger/` when present).

For a host-agnostic, replayable audit narrative, see the ground-truth audit under `docs/audits/`.
