# Ingress request note: quick usage

```bash
# Bind a request and create sidecars
printf '{"tau":1}\n' | scripts/bin/bind_request.sh demo - > receipts/demo.sha256

# Emit the note JSON pairing digest + preimage path
scripts/bin/write_request_note.sh demo > /dev/null

# Inspect
cat receipts/demo.request.note.json
```

