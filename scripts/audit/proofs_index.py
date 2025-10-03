import json
from pathlib import Path
def load_or_none(p):
    try:
        return json.loads(Path(p).read_text())
    except Exception:
        return None
cone_p="artifacts/proofs/cone_id_gf2.json"
cech_p="artifacts/proofs/cech_identities.json"
out={
  "cone_id": cone_p,
  "cech": cech_p,
  "cone_id_payload": load_or_none(cone_p),
  "cech_payload": load_or_none(cech_p)
}
Path("artifacts/audit/proofs_index.json").write_text(json.dumps(out,separators=(",",":")))
