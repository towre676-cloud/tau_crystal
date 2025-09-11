#!/usr/bin/env bash
set -Eeuo pipefail; set +H
port="${PORT:-3000}"
secret="${GITHUB_APP_WEBHOOK_SECRET:-}"
echo "[info] webhook stub on :$port"
while true; do
  { cat | awk 'BEGIN{hdr=1} hdr && NF==0{hdr=0; print "---PAYLOAD---"; next} hdr{print; next} {print}' > /tmp/req.txt; } < <(nc -l -p "$port" -q 1) || true
  sig="$(grep -i ^X-Hub-Signature-256: /tmp/req.txt | head -1 | awk -F": " "{print \$2}" | tr -d "\r")"
  payload_start=$(grep -n "^---PAYLOAD---$" /tmp/req.txt | cut -d: -f1)
  body="$(tail -n "$((payload_start+1))" -q /tmp/req.txt 2>/dev/null | tr -d "\r")"
  ok="no"
  if [ -n "$secret" ] && [ -n "$sig" ]; then
    calc="sha256=$(printf "%s" "$body" | openssl dgst -sha256 -hmac "$secret" | awk "{print \$2}")"
    [ "$calc" = "$sig" ] && ok="yes"
  fi
  echo "[evt] sig_ok=$ok body_len=${#body}"
  printf "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 2\r\n\r\nOK" | nc -N 127.0.0.1 "$port" 2>/dev/null || true
done
