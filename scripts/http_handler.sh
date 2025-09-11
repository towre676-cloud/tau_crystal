#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022

# HTTP handler with optional Authorization check (Bearer or Basic).
# Reads a single HTTP request from stdin, writes a single HTTP response to stdout.
# Bridges JSON body to scripts/tau_pipe.sh and returns its envelope.

log_auth(){ printf "%s | %s\n" "$(date -u +%FT%TZ)" "$1" >> .tau_fifo/logs/http.auth.log; }
bad(){ code="$1"; msg="$2"; body=$(printf '{"ok":false,"error":"%s"}' "$msg"); printf "HTTP/1.1 %s\r\nContent-Type: application/json\r\nContent-Length: %s\r\n\r\n%s" "$code" "$(printf "%s" "$body" | wc -c | awk "{print \$1}")" "$body"; }
ok(){ body="$1"; printf "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: %s\r\n\r\n%s" "$(printf "%s" "$body" | wc -c | awk "{print \$1}")" "$body"; }

# returns 0 if Authorization header satisfies configured policy, else non-zero
auth_check(){
  local hdr="$1" want_bearer="${TAU_HTTP_TOKEN:-}" want_basic="${TAU_HTTP_BASIC:-}"
  # No policy configured → allow
  if [ -z "$want_bearer" ] && [ -z "$want_basic" ]; then return 0; fi
  # Require header if any policy set
  [ -n "$hdr" ] || { log_auth "DENY missing Authorization"; return 1; }
  # Bearer check
  if [ -n "$want_bearer" ]; then
    case "$hdr" in
      "Bearer "* ) token="${hdr#Bearer }"; [ "$token" = "$want_bearer" ] || { log_auth "DENY bearer mismatch"; return 1; } ;;
      * ) log_auth "DENY no Bearer prefix"; return 1;;
    esac
  fi
  # Basic check
  if [ -n "$want_basic" ]; then
    # expected base64 of user:pass
    expect_b64=$(printf "%s" "$want_basic" | base64 | tr -d "\n\r")
    case "$hdr" in
      "Basic "* ) got="${hdr#Basic }"; [ "$got" = "$expect_b64" ] || { log_auth "DENY basic mismatch"; return 1; } ;;
      * ) log_auth "DENY no Basic prefix"; return 1;;
    esac
  fi
  log_auth "ALLOW auth ok"; return 0
}

read_req(){
  local line method path proto clen=0 ctype="" auth=""
  IFS= read -r line || { bad "400 Bad Request" "empty request"; return 1; }
  line=${line%$'\r'}
  IFS=' ' read -r method path proto <<<"$line"
  [ "${method:-}" = "POST" ] || { bad "405 Method Not Allowed" "only POST allowed"; return 1; }
  [ "${path:-}" = "/tau/step" ] || { bad "404 Not Found" "path must be /tau/step"; return 1; }
  while IFS= read -r line; do
    line=${line%$'\r'}
    [ -z "$line" ] && break
    lower=$(printf "%s" "$line" | tr "[:upper:]" "[:lower:]")
    case "$lower" in
      content-length:*) clen=$(printf "%s" "${line#*:}" | tr -dc 0-9);;
      content-type:application/json*) ctype="application/json";;
      authorization:*) auth="${line#*: }";;
    esac
  done
  # auth gate (optional)
  if ! auth_check "$auth"; then
    # choose WWW-Authenticate based on configured mode
    if [ -n "${TAU_HTTP_BASIC:-}" ]; then
      hdr="WWW-Authenticate: Basic realm=\"tau-crystal\""
    else
      hdr="WWW-Authenticate: Bearer realm=\"tau-crystal\""
    fi
    body=$(printf '{"ok":false,"error":"unauthorized"}')
    len=$(printf "%s" "$body" | wc -c | awk "{print \$1}")
    printf "HTTP/1.1 401 Unauthorized\r\n%s\r\nContent-Type: application/json\r\nContent-Length: %s\r\n\r\n%s" "$hdr" "$len" "$body"
    return 1
  fi
  [ "${ctype:-}" = "application/json" ] || { bad "415 Unsupported Media Type" "Content-Type must be application/json"; return 1; }
  [ "${clen:-0}" -gt 0 ] || { bad "400 Bad Request" "missing Content-Length"; return 1; }
  body=$(dd bs=1 count="$clen" 2>/dev/null || true)
  [ "$(printf "%s" "$body" | wc -c | awk "{print \$1}")" -eq "$clen" ] || { bad "400 Bad Request" "body length mismatch"; return 1; }
  env TAU_TIMEOUT=${TAU_TIMEOUT:-60} bash scripts/tau_pipe.sh <<<"$body" > .tau_fifo/logs/http.last.envelope.json 2> .tau_fifo/logs/http.last.err || true
  if [ -s .tau_fifo/logs/http.last.envelope.json ]; then
    resp=$(cat .tau_fifo/logs/http.last.envelope.json)
    ok "$resp"
  else
    bad "500 Internal Server Error" "no response from adapter"
  fi
}

read_req
