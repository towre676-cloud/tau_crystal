#!/usr/bin/env python3
import json, glob, os
from datetime import datetime, timezone

def load_latest_manifest():
    ms = glob.glob("manifests/*.json")
    if not ms:
        return None, None
    latest = max(ms, key=os.path.getmtime)
    with open(latest, encoding="utf-8") as f:
        return json.load(f), latest

def render(doc, latest_path):
    if not doc:
        return "<!doctype html><meta charset=utf-8><p>No manifests found.</p>"
    tau = doc.get("tau", {}).get("t", [])
    root = doc.get("attest", {}).get("merkle_root", "—")
    ts   = doc.get("attest", {}).get("timestamp", "—")
    now  = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%SZ")
    return f"""<!doctype html><meta charset="utf-8"><title>τ‑Crystal · Live</title>
<style>body{{font-family:system-ui;margin:24px}}code,pre{{background:#f6f8fa;padding:4px 6px;border-radius:4px}}</style>
<h1>τ‑Crystal · Live</h1>
<p>Generated {now}</p>
<p>Latest: <code>{os.path.basename(latest_path)}</code></p>
<p>Merkle root: <code>{root}</code></p>
<p>Timestamp: <code>{ts}</code></p>
<p>τ sequence:</p>
<pre>{json.dumps(tau, indent=2, ensure_ascii=False)}</pre>"""

def main():
    doc, latest = load_latest_manifest()
    html = render(doc, latest or "")
    os.makedirs("docs/sample", exist_ok=True)
    open("docs/sample/live.html", "w", encoding="utf-8").write(html)
    print("[html] docs/sample/live.html")

if __name__ == "__main__":
    main()
