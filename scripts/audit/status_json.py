import json, os
from pathlib import Path
def load_or_none(p):
    try:
        return json.loads(Path(p).read_text())
    except Exception:
        return None
def read_text_or_none(paths):
    for p in paths:
        q=Path(p)
        if q.exists():
            try: return q.read_text().strip()
            except Exception: return None
    return None
out={
  "echo_nontrivial": load_or_none("artifacts/echo/graded_scalar_from_hist.json"),
  "curvature": {
      "c":   load_or_none("artifacts/curvature/cocycle_cijk.json"),
      "len": load_or_none("artifacts/curvature/length_metrics.json"),
      "kl":  load_or_none("artifacts/curvature/timefold_kl.json")
  },
  "motive": load_or_none("artifacts/motive/period_values.json"),
  "seal": {
      "cert": load_or_none("artifacts/seal/verifier_certificate.json"),
      "H_tau": read_text_or_none(["artifacts/seal/.H_\xce\xa4","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84".encode("utf-8","ignore").decode("utf-8","ignore"),"artifacts/seal/.H_\xce\xa4".encode("utf-8","ignore").decode("utf-8","ignore"),"artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84".replace("\\xcf\\x84","\\xcf\\x84"),"artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84", "artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84", "artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84", "artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84", "artifacts/seal/.H_\xcf\x84", "artifacts/seal/.H_\xcf\x84", "artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84", "artifacts/seal/.H_\xcf\x84", "artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_\xcf\x84","artifacts/seal/.H_tau"])
  },
  "proofs": load_or_none("artifacts/audit/proofs_index.json")
}
Path("artifacts/audit/status.json").write_text(json.dumps(out,separators=(",",":")))
