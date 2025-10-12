#!/usr/bin/env bash
# τ-Crystal DChar library (robust): init once per shell; no early return; shims always defined.

# One-time init in THIS shell (do not export!)
if [ -z "${TAU_DCHAR_INIT:-}" ]; then
  TAU_DCHAR_INIT=1
  set -euo pipefail; set +H; umask 022; export LC_ALL=C
  SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

  # Logging (fallback if utils.sh missing)
  if [ -f "${SCRIPT_DIR}/utils.sh" ]; then
    # shellcheck source=scripts/utils.sh
    . "${SCRIPT_DIR}/utils.sh"
  else
    log_info(){  printf '[INFO] %s\n'  "$*"; }
    log_ok(){    printf '[OK] %s\n'    "$*"; }
    log_warn(){  printf '[WARN] %s\n'  "$*" >&2; }
    log_error(){ printf '[ERROR] %s\n' "$*" >&2; }
    log_fatal(){ log_error "$@"; exit 1; }
  fi

  # Hasher chooser (idempotent)
  tau_choose_hasher(){
    if [ -n "${TAU_HASHER:-}" ] && command -v "$TAU_HASHER" >/dev/null 2>&1; then return; fi
    if command -v sha256sum >/dev/null 2>&1; then TAU_HASHER=sha256sum; return; fi
    if command -v shasum     >/dev/null 2>&1; then TAU_HASHER=shasum;     return; fi
    TAU_HASHER=openssl
  }
  tau_choose_hasher
fi

# --- Core shims (defined only if missing) ---

# Deterministic serialization: join args with ASCII unit-separator (0x1F) + newline.
if ! command -v tau_serialize >/dev/null 2>&1; then
tau_serialize() {
  local US; US=$(printf '\037')
  local out=""; local first=1
  for kv in "$@"; do
    if [ $first -eq 1 ]; then out="$kv"; first=0; else out="${out}${US}${kv}"; fi
  done
  printf '%s\n' "$out"
}
fi

# SHA-256 to lowercase hex via TAU_HASHER/sha256sum/shasum/openssl.
if ! command -v tau_sha256_str >/dev/null 2>&1; then
tau_sha256_str() {
  local s="$1" h
  if [ -n "${TAU_HASHER:-}" ] && command -v "$TAU_HASHER" >/dev/null 2>&1; then
    case "$TAU_HASHER" in
      sha256sum) h=$(printf '%s' "$s" | sha256sum | awk '{print $1}');;
      shasum)    h=$(printf '%s' "$s" | shasum -a 256 | awk '{print $1}');;
      openssl)   h=$(printf '%s' "$s" | openssl dgst -sha256 -r 2>/dev/null | awk '{print $1}');;
      *)         h=$(printf '%s' "$s" | "$TAU_HASHER");;
    esac
  elif command -v sha256sum >/dev/null 2>&1; then
    h=$(printf '%s' "$s" | sha256sum | awk '{print $1}')
  elif command -v shasum >/dev/null 2>&1; then
    h=$(printf '%s' "$s" | shasum -a 256 | awk '{print $1}')
  else
    h=$(printf '%s' "$s" | openssl dgst -sha256 -r 2>/dev/null | awk '{print $1}')
  fi
  if [ -n "${BASH_VERSION:-}" ]; then printf '%s\n' "${h,,}"; else printf '%s\n' "$h" | awk '{print tolower($0)}'; fi
}
fi

# Phase from top 64 bits of a 256-bit hex hash.
if ! command -v tau_phase64 >/dev/null 2>&1; then
tau_phase64() {
  local H="$1" hi="${H:0:8}" lo="${H:8:8}"
  awk -v HI="0x${hi}" -v LO="0x${lo}" 'BEGIN{
    h=strtonum(HI); l=strtonum(LO);
    v=h*4294967296 + l; den=18446744073709551616.0;
    printf("%.17f\n", v/den);
  }'
}
fi

# Merkle root over newline-separated leaf hex; odd-duplication; domain-separated interiors.
if ! command -v tau_merkle_root >/dev/null 2>&1; then
tau_merkle_root() {
  local f="$1"
  if [ ! -s "$f" ]; then tau_sha256_str ""; return 0; fi
  local in out a b
  in=$(mktemp); out=$(mktemp); cp "$f" "$in"
  while :; do
    if [ "$(wc -l < "$in" | tr -d ' ')" -eq 1 ]; then cat "$in"; rm -f "$in" "$out"; return 0; fi
    : > "$out"
    while read -r a; do
      if read -r b; then
        tau_sha256_str "MERKLE256|${a}|${b}" >> "$out"
      else
        tau_sha256_str "MERKLE256|${a}|${a}" >> "$out"
      fi
    done < "$in"
    mv "$out" "$in"
  done
}
fi

# UTC-stamped receipt directory.
if ! command -v tau_receipt_dir >/dev/null 2>&1; then
tau_receipt_dir() {
  local ts dir; ts="$(date -u '+%Y%m%dT%H%M%SZ')"; dir=".tau_ledger/dchar/${ts}"
  mkdir -p "$dir"; printf '%s\n' "$dir"
}
fi
# --- override tau_phase64 to be robust to empty/missing arg (nounset-safe) ---
tau_phase64() {
  # Use default expansion so set -u doesn't trip if no arg was passed
  local hstr="${1-}"

  # If unset or empty, use 16 zero hex digits
  if [ -z "${hstr+x}" ] || [ -z "$hstr" ]; then
    hstr=0000000000000000
  fi

  # Keep only hex chars (defensive)
  hstr="$(printf '%s' "$hstr" | tr -cd '0-9a-fA-F')"

  # Right-pad to at least 16 hex chars
  while [ "${#hstr}" -lt 16 ]; do hstr="${hstr}0"; done

  # Top 64 bits = first 16 hex chars
  local hi="${hstr:0:8}" lo="${hstr:8:8}"

  awk -v HI="0x${hi}" -v LO="0x${lo}" 'BEGIN{
    h=strtonum(HI); l=strtonum(LO);
    v=h*4294967296 + l;
    den=18446744073709551616.0;
    printf("%.17f\n", v/den);
  }'
}
