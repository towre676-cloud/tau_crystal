#!/usr/bin/env bash
set -u
IN="${1:-tmp/P2P.ndjson}"
mkdir -p manifests tmp
[ -f "$IN" ] || cat > "$IN" <<'NDJ'
{"process_id":"PO-2025-0912-00421","domain":"P2P","segment":"PO.created","ts":"2025-09-06T14:20:00Z"}
{"process_id":"PO-2025-0912-00421","domain":"P2P","segment":"GRN.posted","ts":"2025-09-06T14:22:00Z"}
NDJ
python - <<'PY'
import json,hashlib,os,sys,datetime
IN=sys.argv[1] if len(sys.argv)>1 else "tmp/P2P.ndjson"
core={
  "kind":"tau-crystal-receipt","version":"1.2.0",
  "process":{"id":"PO-2025-0912-00421","domain":"P2P","segment":"GRN.posted","prev_manifest":""},
  "tau":{"t":[0.0,0.06,0.12,0.18,0.24,0.30],"clock":"Chebyshev-decay","params":{"tau_min":0.06,"slope":0.30}},
  "residue":{"R_norm":0.0,"D_norm":0.0,"kappa":0.1591549431,"qcro":[]},
  "witness":{"events_sha":"","pivot_transcript":"sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855","rank_signature":{"p":2147482951,"rank":6}},
  "sustainability":{}
}
try:
  with open(IN,'rb') as f: core["witness"]["events_sha"]="sha256:"+hashlib.sha256(f.read()).hexdigest()
except FileNotFoundError:
  core["witness"]["events_sha"]="sha256:"+hashlib.sha256(b"").hexdigest()
core_bytes=json.dumps(core, separators=(',',':'), sort_keys=True).encode()
digest=hashlib.sha256(core_bytes).hexdigest()
out={**core,"attest":{"merkle_root":"sha256:"+digest,"signed_by":"","timestamp":datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")}}
os.makedirs("manifests",exist_ok=True)
with open(f"manifests/{digest}.json","w",encoding="utf-8") as f: json.dump(out,f,ensure_ascii=False,indent=2)
PY
