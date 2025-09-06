#!/usr/bin/env python3
import json, hashlib, subprocess, sys, os, datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIST = ROOT / "dist"
DIST.mkdir(exist_ok=True)

def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

assets = [
    ROOT / "tau-crystal-manifest.json",
    ROOT / "tau-crystal-receipt.json",
    ROOT / "docs" / "monographs.tar.gz",
    ROOT / "docs" / "monographs.zip",
    ROOT / "docs" / "specs" / "manifest-v1.1.md",
    ROOT / "scripts" / "tauc.py",
]

# checksums
with (DIST / "SHA256SUMS.txt").open("w", encoding="utf-8", newline="\n") as f:
    for p in assets:
        if p.exists():
            f.write(f"{sha256(p)}  {p.relative_to(ROOT)}\n")

# CycloneDX SBOM (JSON)
version_desc = subprocess.check_output(["git","describe","--tags","--always"], text=True).strip()
sbom = {
    "bomFormat": "CycloneDX",
    "specVersion": "1.5",
    "serialNumber": f"urn:uuid:{hashlib.sha256(('tau-crystal'+version_desc).encode()).hexdigest()[:32]}",
    "version": 1,
    "metadata": {
        "timestamp": datetime.datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
        "tools": [{"vendor": "tau-crystal", "name": "tauc", "version": "1.1"}],
        "component": {
            "type": "application",
            "name": "tau-crystal-docs",
            "version": version_desc
        }
    },
    "components": [
        {
            "type": "file",
            "name": p.relative_to(ROOT).as_posix(),
            "hashes": [{"alg": "SHA-256", "content": sha256(p)}],
            "properties": [{"name": "tau:asset", "value": "true"}]
        }
        for p in assets if p.exists()
    ]
}
(DIST / "sbom.cdx.json").write_text(json.dumps(sbom, indent=2) + "\n", encoding="utf-8")

print("[OK] wrote dist/SHA256SUMS.txt and dist/sbom.cdx.json")
