#!/usr/bin/env bash
set -euo pipefail
set +H
umask 022

read_request(){
  local req line headers clen body method path proto
  IFS= read -r req || { printf "HTTP/1.1 400 Bad Request\r\nContent-Type: application/json\r\nContent-Length: 32\r\n\r\n{\"ok\":false,\"error\":\"bad request\"}"; return 1; }
  req=${req%$'\r'}
  set -- $req
  method="${1:-}"; path="${2:-}"; proto="${3:-}"
  headers=$(mktemp)
  while IFS= read -r line; do
    line=${line%$'\r'}
    [ -z "$line" ] && break
    printf "%s\n" "$line" >> "$headers"
  done
  clen=$(awk -F: 'tolower($1)=="content-length"{gsub(/^[[:space:]]+|[[:space:]]+$/, "", $2); print $2}' "$headers")
  [ -z "${clen:-}" ] && clen=0
  if [ "$clen" -gt 0 ]; then
    body=$(dd bs=1 count="$clen" 2>/dev/null | tr -d '\r')
  else
    body=""
  fi
  printf "%s\n%s\n%s\n%s\n" "$method" "$path" "$proto" "$body"
  rm -f "$headers"
}

json_get(){
  # usage: json_get key "$json"
  local k="$1" j="$2"
  printf "%s" "$j" | sed -n "s/.*\\\"$k\\\"[[:space:]]*:[[:space:]]*\\\"\\([^\\\"]*\\)\\\".*/\\1/p" | head -n1
}

json_escape(){
  awk 'BEGIN{RS=""; ORS=""} {gsub(/\\/,"\\\\"); gsub(/"/,"\\\""); gsub(/\r/,""); gsub(/\t/,"\\t"); gsub(/\n/,"\\n"); printf "%s",$0}'
}

main(){
  local method path proto body tool inp out outlog errlog resp rc
  { read_request; } | { IFS= read -r method; IFS= read -r path; IFS= read -r proto; IFS= read -r body; printf "%s\n%s\n%s\n%s\n" "$method" "$path" "$proto" "$body"; } | \\
  { IFS= read -r method; IFS= read -r path; IFS= read -r proto; IFS= read -r body;
    if [ "$method" != "POST" ] || [ "$path" != "/tau/step" ]; then
      resp="{\"ok\":false,\"error\":\"route not found\"}"; printf "HTTP/1.1 404 Not Found\r\nContent-Type: application/json\r\nContent-Length: %d\r\n\r\n%s" "${#resp}" "$resp"; exit 0; fi
    tool=$(json_get tool "$body"); inp=$(json_get input_path "$body"); out=$(json_get output_path "$body")
    outlog=$(mktemp); errlog=$(mktemp)
    if bash "./scripts/tau_step.sh" "${tool:-}" "${inp:-}" "${out:-}" >"$outlog" 2>"$errlog"; then rc=0; else rc=$?; fi
    if [ "$rc" -eq 0 ]; then
      resp=$(printf '{"ok":true,"stdout":"%s"}' "$(json_escape <"$outlog")")
      printf "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: %d\r\n\r\n%s" "${#resp}" "$resp"
    else
      resp=$(printf '{"ok":false,"code":%d,"stderr":"%s"}' "$rc" "$(json_escape <"$errlog")")
      printf "HTTP/1.1 500 Internal Server Error\r\nContent-Type: application/json\r\nContent-Length: %d\r\n\r\n%s" "${#resp}" "$resp"
    fi
    rm -f "$outlog" "$errlog"
  }
}
