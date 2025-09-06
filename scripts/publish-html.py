#!/usr/bin/env python3
import json,glob,os
from datetime import datetime,timezone
m=glob.glob("manifests/*.json")
if not m:
  html="<!doctype html><meta charset=utf-8><p>No manifests found.</p>"
else:
  latest=max(m,key=os.path.getmtime)
  doc=json.load(open(latest,encoding="utf-8"))
  tau=doc.get("tau",{}).get("t",[])
  root=doc.get("attest",{}).get("merkle_root","—")
  ts=doc.get("attest",{}).get("timestamp","—")
  html=f"""<!doctype html><meta charset="utf-8"><title>τ-Crystal · Live</title>
<style>body{{font-family:system-ui;margin:24px}}code,pre{{background:#f6f8fa;padding:4px 6px;border-radius:4px}}</style>
<h1>τ-Crystal · Live</h1>
<p>Generated {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%SZ')}</p>
<p>Latest Merkle root: <code>{root}</code></p>
<p>Timestamp: <code>{ts}</code></p>
<p>τ sequence:</p>
<pre>{json.dumps(tau,indent=2,ensure_ascii=False)}</pre>"""
os.makedirs("docs/sample",exist_ok=True)
open("docs/sample/live.html","w",encoding="utf-8").write(html)
