import json,sys,time,uuid
from pathlib import Path
out=Path("artifacts/sigma/terms.jsonl"); out.parent.mkdir(parents=True,exist_ok=True)
op=sys.argv[1] if len(sys.argv)>1 else "id"
args=sys.argv[2:]
rec={"ts":int(time.time()),"id":str(uuid.uuid4()),"op":op,"args":args}
with out.open("a",encoding="utf-8") as f: f.write(json.dumps(rec,separators=(",",":"))+"\\n")
print(rec["id"])
