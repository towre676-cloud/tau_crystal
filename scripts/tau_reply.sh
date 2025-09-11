#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
ok=""; code=""; sout=""; serr=""
while [ $# -gt 0 ]; do
  case "$1" in --ok) ok=true; shift;; --fail) ok=false; shift;; --code) code="$2"; shift 2;; --stdout) sout="$2"; shift 2;; --stderr) serr="$2"; shift 2;; *) echo "[tau_reply] unknown $1" >&2; exit 2;; esac
done
esc(){ awk 'BEGIN{RS="";ORS=""}{gsub(/\\/,"\\\\");gsub(/"/,"\\\"");gsub(/\r/,"");gsub(/\t/,"\\t");gsub(/\n/,"\\n");printf "%s",$0}'; }
printf "{"
[ -n "$ok" ]   && printf "\"ok\":%s"   "$ok" || printf "\"ok\":false"
[ -n "$code" ] && printf ",\"code\":%s" "$(printf "%s" "$code" | tr -dc 0-9)"
[ -n "$sout" ] && printf ",\"stdout\":\"%s\"" "$(printf "%s" "$sout" | esc)"
[ -n "$serr" ] && printf ",\"stderr\":\"%s\"" "$(printf "%s" "$serr" | esc)"
printf "}\n"
