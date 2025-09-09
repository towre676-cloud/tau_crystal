#!/usr/bin/env bash
# Append a leaf (canonical JSON bytes) to an append-only Merkle log.
# State: .tau_ledger/merkle_state.txt (algo=<blake3|sha256>, n=<int>, L<k>=<hex>)
# Nodes: H(0x00 || leaf_bytes); Parents: H(0x01 || left||right) on raw bytes.
set -euo pipefail
set +H
umask 022

STATE="${MERKLE_STATE:-.tau_ledger/merkle_state.txt}"

_hasher() { if command -v b3sum >/dev/null 2>&1; then echo "blake3"; else echo "sha256"; fi; }

hash_stdin() {
  case "$1" in
    blake3)  b3sum     | awk "{print \$1}" ;;
    sha256)  sha256sum | awk "{print \$1}" ;;
    *) echo "[err] unknown algo $1" >&2; return 2 ;;
  esac
}

leaf_hash() {
  local algo="$1"
  { printf '\x00'; cat; } | hash_stdin "$algo"
}

hex_to_bin() {
  if command -v xxd >/dev/null 2>&1; then xxd -r -p; return 0; fi
  if command -v openssl >/dev/null 2>&1; then openssl enc -d -hex -A 2>/dev/null; return 0; fi
  if command -v python3 >/dev/null 2>&1; then python3 -c 'import sys,binascii,re; d=sys.stdin.read(); d=re.sub(r"\s+","",d); sys.stdout.buffer.write(binascii.unhexlify(d))'; return 0; fi
  if command -v perl >/dev/null 2>&1;   then perl -pe "s/([0-9A-Fa-f]{2})/chr hex \$1/eg"; return 0; fi
  echo "[err] need xxd or openssl or python3 or perl to decode hex" >&2; return 127
}

parent_hash() {
  local algo="$1" LH="$2" RH="$3"
  { printf '\x01'; printf "%s" "$LH" | hex_to_bin; printf "%s" "$RH" | hex_to_bin; } | hash_stdin "$algo"
}

declare -A FRONTIER=()
ALGO=""
N=0

load_state() {
  ALGO="$(_hasher)"
  N=0
  FRONTIER=()
  if [[ -f "$STATE" ]]; then
    while IFS='=' read -r k v; do
      [[ -z "${k:-}" ]] && continue
      case "$k" in
        algo) [[ -n "${v:-}" ]] && ALGO="$v" ;;
        n)    N="${v:-0}" ;;
        L*)   lvl="${k#L}"; FRONTIER["$lvl"]="$v" ;;
      esac
    done < <(sed 's/\r$//' "$STATE")
  fi
}

save_state() {
  local max=0 k
  for k in "${!FRONTIER[@]}"; do [[ "$k" -gt "$max" ]] && max="$k"; done
  mkdir -p "$(dirname "$STATE")"
  { printf "algo=%s\n" "$ALGO"
    printf "n=%s\n" "$N"
    for ((i=0;i<=max;i++)); do
      [[ -n "${FRONTIER[$i]:-}" ]] && printf "L%d=%s\n" "$i" "${FRONTIER[$i]}"
    done
  } > "${STATE}.tmp"
  mv -f "${STATE}.tmp" "$STATE"
}

compute_root() {
  local acc="" max=0 k
  for k in "${!FRONTIER[@]}"; do [[ "$k" -gt "$max" ]] && max="$k"; done
  for ((i=0;i<=max;i++)); do
    local h="${FRONTIER[$i]:-}"
    [[ -z "$h" ]] && continue
    if [[ -z "$acc" ]]; then acc="$h"; else acc="$(parent_hash "$ALGO" "$h" "$acc")"; fi
  done
  printf "%s\n" "$acc"
}

cmd_append() {
  load_state
  local tmp
  tmp="$(mktemp 2>/dev/null || printf ".merkle.tmp.%s" "$$")"
  : > "$tmp"
  cat > "$tmp"
  local L_DIG node level cur idx ROOT
  L_DIG="$(leaf_hash "$ALGO" < "$tmp")"
  node="$L_DIG"; level=0
  while :; do
    cur="${FRONTIER[$level]:-}"
    if [[ -z "$cur" ]]; then FRONTIER[$level]="$node"; break; fi
    node="$(parent_hash "$ALGO" "$cur" "$node")"
    FRONTIER[$level]=""; level=$((level+1))
  done
  idx="$N"; N=$((N+1))
  save_state
  ROOT="$(compute_root)"
  printf "leaf_digest=%s\n" "$L_DIG"
  printf "tlog_root=%s\n"   "$ROOT"
  printf "tlog_index=%s\n"  "$idx"
  printf "tlog_algo=%s\n"   "$ALGO"
  rm -f "$tmp"
}

case "${1:-}" in
  append) shift; cmd_append ;;
  *) echo "usage: $0 append < leaf_json" >&2; exit 2 ;;
esac
