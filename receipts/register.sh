#!/usr/bin/env bash
# Robust CSV appender (ASCII-only, Windows-safe)
set -eu

REG="receipts/registry.csv"

usage() {
  echo "Usage: bash receipts/register.sh <run_id> <kind> <obs_mod_2pi> <glues> <file> [notes]" >&2
}

# Require at least 5 args
if [ "$#" -lt 5 ]; then usage; exit 2; fi

run_id="$1"
kind="$2"
obs="$3"
glues="$4"
file="$5"
notes="${6-}"

# Make sure receipts dir exists
mkdir -p receipts

# Create header if missing
if [ ! -f "$REG" ]; then
  echo "timestamp_utc,run_id,kind,obs_mod_2pi,glues,notes,file" > "$REG"
fi

# UTC timestamp (fallback if -u unsupported)
if date -u +%Y >/dev/null 2>&1; then
  ts="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"
else
  TZ=UTC ts="$(date +'%Y-%m-%dT%H:%M:%SZ')"
fi

# Normalize glues
case "$glues" in
  true|TRUE|1)  glues=true ;;
  false|FALSE|0) glues=false ;;
esac

# CSV-quote helper: wrap in "..." and double any internal quotes
csvq() {
  s=${1-}
  s=${s//\"/\"\"}
  printf '"%s"' "$s"
}

# Build row (quote all text fields)
row=$(printf "%s,%s,%s,%s,%s,%s,%s" \
  "$ts" \
  "$(csvq "$run_id")" \
  "$(csvq "$kind")" \
  "$obs" \
  "$(csvq "$glues")" \
  "$(csvq "$notes")" \
  "$(csvq "$file")")

printf "%s\n" "$row" >> "$REG"
echo "[ok] registered $(csvq "$run_id") -> $REG"
