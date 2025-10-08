#!/usr/bin/env python3
import argparse, hashlib, json, os, sys
from pathlib import Path

def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def sha256_file(p: Path) -> str:
    with p.open('rb') as f:
        return sha256_bytes(f.read())

def main() -> int:
    ap = argparse.ArgumentParser(description="Freeze a deterministic receipt over inputs.")
    ap.add_argument("--outdir", default="out/receipts", help="output directory for receipt + merkle root")
    ap.add_argument("paths", nargs="*", help="files to include (will be filtered to existing files)")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    # default set if none provided (keeps your current workflow intact)
    default_paths = [
        "out/coeffs/q1_stub.json",
        "out/receipts/automorphy_stub.json",
        "out/receipts/mde_stub.json",
    ]
    raw_paths = args.paths if args.paths else default_paths

    # filter to existing, normalize, sort for determinism
    files = sorted({str(Path(p)) for p in raw_paths if Path(p).is_file()})

    # compute per-file hashes
    file_hashes = {p: sha256_file(Path(p)) for p in files}

    # concatenation in sorted order
    concat = b"".join(Path(p).read_bytes() for p in files)
    merkle_root = sha256_bytes(concat)

    # write artifacts
    (outdir / "merkle_root.txt").write_text(merkle_root + "\n", encoding="utf-8")
    receipt = {
        "schema": "tau_crystal.receipt/v1",
        "repo_cwd": str(Path.cwd()),
        "inputs": files,
        "file_hashes": file_hashes,
        "concat_sha256": merkle_root,
    }
    (outdir / "receipt.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # stdout line for pipelines
    print(json.dumps({"status": "ok", "merkle_root": merkle_root, "n_inputs": len(files)}))
    return 0

if __name__ == "__main__":
    sys.exit(main())
