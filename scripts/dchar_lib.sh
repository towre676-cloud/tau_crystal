#!/usr/bin/env bash
# τ-Crystal DChar library: guards, hashing, phase, Merkle, receipts

if [ -n "${TAU_DCHAR_LOADED:-}" ]; then return 0 2>/dev/null; fi
export TAU_DCHAR_LOADED=1
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
if [ -f "${SCRIPT_DIR}/utils.sh" ]; then . "${SCRIPT_DIR}/utils.sh"; else
  log_info(){ printf "[INFO] %s\n" "$*"; }; log_ok(){ printf "[OK] %s\n" "$*"; }; log_warn(){ printf "[WARN] %s\n" "$*" >&2; }; log_error(){ printf "[ERROR] %s\n" "$*" >&2; }; log_fatal(){ log_error "$@"; exit 1; }
fi

tau_choose_hasher(){
  if command -v sha256sum >/dev/null 2>&1; then echo "sha256sum"; return; fi
  if command -v shasum >/dev/null 2>&1; then echo "shasum"; return; fi
  if command -v openssl >/dev/null 2>&1; then echo "openssl"; return; fi
  log_fatal "No SHA-256 tool found (need sha256sum, shasum, or openssl)."
}
TAU_HASHER="${TAU_HASHER:-$(tau_choose_hasher)}"

tau_hex_lower(){ tr "[:upper:]" "[:lower:]"; }

tau_sha256_str(){
  local s="$1" out
  case "$TAU_HASHER" in
    sha256sum) out="$(printf "%s" "$s" | sha256sum | awk "{print \$1}" | tau_hex_lower)";;
    shasum)    out="$(printf "%s" "$s" | shasum -a 256 | awk "{print \$1}" | tau_hex_lower)";;
    openssl)   out="$(printf "%s" "$s" | openssl dgst -sha256 | awk "{print \$NF}" | tau_hex_lower)";;
  esac
  printf "%s\n" "$out"
}

tau_serialize(){
  local out=""; local first=1; local sep="$(printf '\037')"
  for kv in "$@"; do
    if [ $first -eq 1 ]; then out="$kv"; first=0; else out="${out}${sep}${kv}"; fi
  done
  printf "%s\n" "$out"
}

tau_phase64(){
  local hex256="$1"; local h16="${hex256:0:16}"; local hi="${h16:0:8}"; local lo="${h16:8:8}"
  local hi_d=$((16#${hi})); local lo_d=$((16#${lo}))
  awk -v HI="$hi_d" -v LO="$lo_d" 'BEGIN{ num=HI*4294967296.0+LO; den=18446744073709551616.0; f=num/den; printf("%.17f\n", f-int(f)); }' 
}

tau_merkle_root(){
  local tmp="$1"; [ -s "$tmp" ] || { echo ""; return 0; }
  local work; work="$(mktemp)"; cp "$tmp" "$work"
  while :; do
    local n; n=$(wc -l < "$work" | tr -d " ")
    if [ "$n" -le 1 ]; then cat "$work"; rm -f "$work"; return 0; fi
    local next; next="$(mktemp)"; local i=1
    while [ "$i" -le "$n" ]; do
      local A B; A="$(sed -n "${i}p" "$work")"; B="$(sed -n "$((i+1))p" "$work" || true)"
      if [ -z "${B:-}" ]; then B="$A"; fi
      tau_sha256_str "MERKLE256|${A}|${B}" >> "$next"
      i=$((i+2))
    done
    mv "$next" "$work"
  done
}

tau_now(){ date -u "+%Y%m%dT%H%M%SZ"; }
tau_receipt_dir(){ local d=".tau_ledger/dchar/$(tau_now)"; mkdir -p "$d"; printf "%s\n" "$d"; }
