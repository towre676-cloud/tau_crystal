import json,math
from pathlib import Path
spec=json.loads(Path("artifacts/motive/variety_spec.json").read_text())
per=0.5*math.pi
out={"period":{"real":per},"regulator":{"real":per},"spec":spec}
Path("artifacts/motive/period_values.json").write_text(json.dumps(out,separators=(",",":")))
