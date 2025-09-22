#!/usr/bin/env bash
set -euo pipefail; set +H
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
REG="$ROOT/ramanujan/registry/objects.tsv"
if [ $# -lt 6 ]; then echo "usage: $0 id kind weight level multiplier meta"; exit 2; fi
id="$1"; kind="$2"; weight="$3"; level="$4"; mult="$5"; shift 5; meta="$*"
if grep -q "^${id}\t" "$REG" 2>/dev/null; then exit 0; fi
printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$id" "$kind" "$weight" "$level" "$mult" "$meta" >> "$REG"
printf "registered\t%s\n" "$id"
