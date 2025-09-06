#!/usr/bin/env python3
import json, datetime, subprocess, os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "tau-crystal-manifest.json"
RECEIPT  = ROOT / "tau-crystal-receipt.json"
TRANSCRIPT = ROOT / "docs" / "ledger" / "last-good-run.json"

TRANSCRIPT.parent.mkdir(parents=True, exist_ok=True)

man = json.loads(MANIFEST.read_text())
rec = json.loads(RECEIPT.read_text())

transcript = {
    "timestamp_utc": datetime.datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
    "git_sha": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "manifest_merkle_root": man["merkle_root"],
    "receipt_merkle_root": rec["reflective"]["merkle_root"],
    "included_files": [{"path": f["path"], "sha256": f["sha256"]} for f in man["included_files"]],
    "archives": man["archives"],
    "signatures_verified": len(man.get("signatures", [])),
    "pow_bits": man.get("pow", {}).get("bits", 0),
    "status": "verified"
}

TRANSCRIPT.write_text(json.dumps(transcript, indent=2) + "\n", encoding="utf-8")
print(f"[OK] verification transcript written to {TRANSCRIPT}")
