#!/usr/bin/env bash
set -euo pipefail
set +H; umask 022
Q=".tau_fifo/queue"
L=".tau_fifo/server.lock"
mkdir -p "$Q"
if ! mkdir "$L" 2>/dev/null; then echo "[serve:fifo] already running"; exit 0; fi
trap 'rmdir "$L" >/dev/null 2>&1' EXIT
json_get(){ key="$1"; printf "%s" "$2" | sed -n "s/.*\\\"$key\\\"[[:space:]]*:[[:space:]]*\\\"\\([^\\\"]*\\)\\\".*/\\1/p" | head -n1; }
json_escape(){ awk 'BEGIN{RS="";ORS=""}{gsub(/\\/,"\\\\");gsub(/"/,"\\\"");gsub(/\r/,"");gsub(/\t/,"\\t");gsub(/\n/,"\\n");printf "%s",$0}'; }
echo "[serve:fifo] watching $Q (concurrent replies)"
while :; do
  shopt -s nullglob
  for f in "$Q"/*.req; do
    [ -e "$f" ] || break
    id=$(basename "$f" .req)
    body=$(cat -- "$f")
    res="$Q/$id.res"
    if [ ! -p "$res" ]; then echo "[serve:fifo] skip $id (no .res fifo)"; rm -f -- "$f"; continue; fi
    tool=$(json_get tool "$body")
    inp=$( json_get input_path "$body")
    out=$( json_get output_path "$body")
    outlog=$(mktemp); errlog=$(mktemp); rc=0
    if bash "./scripts/tau_step.sh" "${tool:-}" "${inp:-}" "${out:-}" >"$outlog" 2>"$errlog"; then rc=0; else rc=$?; fi
    if [ "$rc" -eq 0 ]; then
      resp=$(printf '{"ok":true,"stdout":"%s"}' "$(json_escape <"$outlog")")
    else
      resp=$(printf '{"ok":false,"code":%d,"stderr":"%s"}' "$rc" "$(json_escape <"$errlog")")
    fi
    printf "%s" "$resp" > "$res"
    rm -f -- "$f" "$outlog" "$errlog"
  done
  sleep 0.05
done
