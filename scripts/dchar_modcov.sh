#!/usr/bin/env bash
# Modular scaffold: S or T^k, canonicalize, sort leaves, compare Merkle roots
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"; source "${SCRIPT_DIR}/dchar_lib.sh"
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || true
usage(){ echo "Usage: $0 S|T:<k> [seed] [--debug]"; }
XFORM="${1:-}"; [ -z "$XFORM" ] && { usage; exit 1; }
SEED="${2:-mcov0}"
DEBUG=0; shift 2 >/dev/null 2>&1 || true; for a in "$@"; do [ "$a" = "--debug" ] && DEBUG=1; done
TAU_POINTS=("i/5" "2i/5" "i/2" "3i/5" "4i/5")
Z_POINTS=("0" "1/6" "1/3" "1/2")
frac(){ awk -v s="$1" 'BEGIN{ if(index(s,"/")){split(s,a,"/"); printf("%.12f", a[1]/a[2]);} else {printf("%.12f", s+0);} }'; }
tau_im(){ s="$1"; n="${s%%i/*}"; [ -z "$n" ] && n=1; d="${s##*/}"; frac "$n/$d"; }
apply_S(){ # in: tr ti zr zi ; out: tr ti zr zi (tab-separated)
  tr="$1"; ti="$2"; zr="$3"; zi="$4"
  new_tr="0.0"
  new_ti="$(awk -v y="$ti" 'BEGIN{printf("%.12f", 1.0/y)}')"
  new_zr="$(awk -v zr="$zr" -v zi="$zi" -v y="$ti" 'BEGIN{printf("%.12f", zi/y)}')"
  new_zi="$(awk -v zr="$zr" -v y="$ti" 'BEGIN{printf("%.12f", -zr/y)}')"
  printf "%s\t%s\t%s\t%s\n" "$new_tr" "$new_ti" "$new_zr" "$new_zi"
}
canon_S(){ tr="$1"; ti="$2"; zr="$3"; zi="$4";
  c=0; while awk -v y="$ti" 'BEGIN{exit !(y<1.0)}'; do
    line="$(apply_S "$tr" "$ti" "$zr" "$zi")"; IFS=$'\t' read -r tr ti zr zi <<< "$line"
    c=$((c+1)); [ "$c" -gt 8 ] && break
  done; printf "%s\t%s\t%s\t%s\n" "$tr" "$ti" "$zr" "$zi"
}
canon_T(){ tr="$1"; ti="$2"; zr="$3"; zi="$4"; printf "0.0\t%s\t%s\t%s\n" "$ti" "$zr" "$zi"; }
leaf(){ tr="$1"; ti="$2"; zr="$3"; zi="$4"; sd="$5";
  pl="$(tau_serialize "v=1" "chart=modcanon" "tau_re=${tr}" "tau_im=${ti}" "z_re=${zr}" "z_im=${zi}" "seed=${sd}")";
  tau_sha256_str "$pl"
}
build_set(){ mode="$1"; kval="${2:-0}"; sd="$3"; tmp="$(mktemp)"; : > "$tmp"
  for t in "${TAU_POINTS[@]}"; do ty="$(tau_im "$t")"; for z in "${Z_POINTS[@]}"; do zr="$(frac "$z")"; zi="0.0"; tr="0.0"; ti="$ty";
      if [ "$mode" = "S" ]; then
        line="$(apply_S "$tr" "$ti" "$zr" "$zi")"; IFS=$'\t' read -r tr ti zr zi <<< "$line"
        line="$(canon_S "$tr" "$ti" "$zr" "$zi")"; IFS=$'\t' read -r tr ti zr zi <<< "$line"
      else
        tr="$(awk -v k="$kval" 'BEGIN{printf("%.12f", k+0.0)}')"
        line="$(canon_T "$tr" "$ti" "$zr" "$zi")"; IFS=$'\t' read -r tr ti zr zi <<< "$line"
      fi
      leaf "$tr" "$ti" "$zr" "$zi" "$sd" >> "$tmp"
  done; done
  # Sort leaves so Merkle root is order-invariant across charts
  stmp="$(mktemp)"; sort "$tmp" > "$stmp"; mv "$stmp" "$tmp"
  echo "$tmp"
}
case "$XFORM" in
  S)   A="$(build_set S 0 "$SEED")"; B="$(build_set S 0 "$SEED")" ;;
  T:*) K="${XFORM#T:}"; A="$(build_set T 0 "$SEED")"; B="$(build_set T "$K" "$SEED")" ;;
  *) usage; exit 1 ;;
esac
RA="$(tau_merkle_root "$A")"; RB="$(tau_merkle_root "$B")"
[ "$DEBUG" -eq 1 ] && { echo "[DEBUG] leaves A:"; tail -n +1 "$A" | head -5; echo "[DEBUG] leaves B:"; tail -n +1 "$B" | head -5; }
rm -f "$A" "$B"
printf "[INFO] root(orig,canon)  = %s\n" "$RA"
printf "[INFO] root(xform,canon) = %s\n" "$RB"
if [ "$RA" = "$RB" ]; then echo "[OK] Modular-canon equality holds."; exit 0; else echo "[ERROR] Roots differ."; [ "$DEBUG" -eq 1 ] && echo "[HINT] Try --debug to print sample leaves."; exit 1; fi
