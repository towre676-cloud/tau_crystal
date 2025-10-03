import json
from pathlib import Path
def L(p):
    try: return json.loads(Path(p).read_text())
    except: return None
out={
 "spec":L("artifacts/motive/variety_spec.json"),
 "values":L("artifacts/motive/period_values.json"),
 "binding":L("artifacts/motive/receipt_binding.json")}
print(json.dumps(out,separators=(",",":")))
