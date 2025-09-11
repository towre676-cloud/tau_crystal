# Ingress request note: quick usage

```bash
# Bind a request and create sidecars
printf '{"tau":1}\n' | scripts/bin/bind_request.sh demo - > receipts/demo.sha256

# Emit the note JSON pairing digest + preimage path
scripts/bin/write_request_note.sh demo > /dev/null

# Inspect
cat receipts/demo.request.note.json
```


> **Env mapping:** `make tau INGRESS=<digest>` sets `TAU_INGRESS_DIGEST` for the receipt writer automatically.

Example (boundary sampling):
```bash
# first and last 1 MiB hashed together
{ xxd -p -l 1048576 -c 1048576 preimage.bin; echo; tail -c 1048576 preimage.bin | xxd -p -c 1048576; } | sha256sum
```
