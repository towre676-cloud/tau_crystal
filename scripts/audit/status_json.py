import json
from pathlib import Path
def L(p):
  try: return json.loads(Path(p).read_text())
  except Exception: return None
def read_first_existing(paths):
  for p in paths:
    q=Path(p)
    if q.exists():
      try: return q.read_text().strip()
      except Exception: return None
  return None
out={
 "echo_nontrivial": L("artifacts/echo/graded_scalar_from_hist.json"),
 "curvature": {
   "c":   L("artifacts/curvature/cocycle_cijk.json"),
   "len": L("artifacts/curvature/length_metrics.json"),
   "kl":  L("artifacts/curvature/timefold_kl.json")
 },
 "motive": L("artifacts/motive/period_values.json"),
 "seal": {
   "cert": L("artifacts/seal/verifier_certificate.json"),
   "H_tau": read_first_existing([
     "artifacts/seal/.H_tau",
     "artifacts/seal/.H_τ"
   ])
 },
 "proofs": L("artifacts/audit/proofs_index.json")
}
Path("artifacts/audit/status.json").write_text(json.dumps(out,separators=(",",":")))
