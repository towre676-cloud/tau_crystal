#!/usr/bin/env bash
set +H
export LC_ALL=C
export TZ=UTC
die(){ printf "ERROR: %s\n" "$*" >&2; exit 1; }
now_utc(){ date -u +%Y-%m-%dT%H:%M:%SZ; }
sha256(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | awk "{print \$1}"; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | awk "{print \$1}"; else die "no sha256 tool"; fi; }
uuid4(){ python -c "import uuid; print(uuid.uuid4())" 2>/dev/null || echo "00000000-0000-4000-8000-000000000000"; }
safe_mkdir(){ [ -d "$1" ] || mkdir -p "$1"; }
write_json(){ out="$1"; shift; safe_mkdir ".tau_ledger/tmp"; tmp=".tau_ledger/tmp/.$(uuid4).json"; : > "$tmp"; printf "{\n" >> "$tmp"; i=0; while [ $# -gt 0 ]; do k="$1"; v="$2"; shift 2; [ $i -gt 0 ] && printf ",\n" >> "$tmp"; printf "  \\"%s\\": \\"%s\\"" "$k" "$v" >> "$tmp"; i=$((i+1)); done; printf "\n}\n" >> "$tmp"; mv "$tmp" "$out"; }
log(){ printf "%s %s\n" "$(now_utc)" "$*"; }
