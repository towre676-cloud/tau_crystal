import json
from pathlib import Path
def L(p):
  try: return json.loads(Path(p).read_text())
  except Exception: return None
def T(p):
  try: return Path(p).read_text().strip()
  except Exception: return None
out={
  "echo": L("artifacts/audit/echo.json") or L("artifacts/echo/graded_scalar_from_hist.json"),
  "curvature": L("artifacts/audit/curvature.json") or {
     "c":  L("artifacts/curvature/cocycle_cijk.json"),
     "len":L("artifacts/curvature/length_metrics.json"),
     "G":  L("artifacts/curvature/G_presentation.json")
  },
  "motive": L("artifacts/audit/motive.json") or L("artifacts/motive/period_values.json"),
  "seal": L("artifacts/audit/seal.json") or {
     "cert":  L("artifacts/seal/verifier_certificate.json"),
     "H_tau": T("artifacts/seal/.H_tau")
  },
  "obs":    L("artifacts/audit/obs.json") or L("artifacts/obs/obs_value.json"),
  "proofs": L("artifacts/audit/proofs.json") or L("artifacts/audit/proofs_index.json"),
  "status": L("artifacts/audit/status.json")
}
Path("artifacts/audit/all.json").write_text(json.dumps(out,separators=(",",":")))
