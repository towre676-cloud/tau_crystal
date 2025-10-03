import json
from pathlib import Path
p=json.loads(Path("artifacts/motive/receipt_params.json").read_text())
spec={"variety":{"curve":"y^2=1-x^2"},"differential":"dx_over_y","path":p.get("path",{"x0":0.0,"x1":1.0})}
Path("artifacts/motive/variety_spec.json").write_text(json.dumps(spec,separators=(",",":")))
