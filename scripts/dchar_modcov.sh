#!/usr/bin/env bash
# Modular scaffold: compare roots under S or T^k after canonicalization.
# Usage:
#   dchar_modcov.sh S [--weight K] [--index M] [--seed SEED]
#   dchar_modcov.sh T:<k> [--weight K] [--index M] [--seed SEED]
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Require core lib; soft-load utils for logs
[ -f "${SCRIPT_DIR}/dchar_lib.sh" ] || { echo "[ERROR] dchar_lib.sh not found" >&2; exit 2; }
# shellcheck source=/dev/null
source "${SCRIPT_DIR}/dchar_lib.sh"
if [ -f "${SCRIPT_DIR}/utils.sh" ]; then
  # shellcheck source=/dev/null
  source "${SCRIPT_DIR}/utils.sh"
else
  log_ok(){ printf "[OK] %s\n" "$*"; }
  log_info(){ printf "[INFO] %s\n" "$*"; }
  log_error(){ printf "[ERROR] %s\n" "$*" >&2; }
fi

XFORM="${1:?Usage: dchar_modcov.sh S|T:<k> [--weight K] [--index M] [--seed SEED] }"; shift || true
K=0    # weight
M=1    # index
SEED="mcov0"

while [ $# -gt 0 ]; do
  case "$1" in
    --weight) K="${2:?}"; shift 2;;
    --index)  M="${2:?}"; shift 2;;
    --seed)   SEED="${2:?}"; shift 2;;
    *) break;;
  esac
done

# Grid (purely imaginary tau; real z)
TAU_POINTS=("i/5" "2i/5" "i/2" "3i/5" "4i/5")
Z_POINTS=("0" "1/6" "1/3" "1/2")

# Helpers to parse our compact literals
frac(){ # supports "a/b" or decimal
  awk -v s="$1" 'BEGIN{
    if (index(s,"/")) { split(s,a,"/"); printf("%.12f", a[1]/a[2]); }
    else { printf("%.12f", s+0.0); }
  }'
}
parse_tau(){ # "i/5" -> "0.0\t0.2"
  s="$1"
  case "$s" in
    *i/*) n="${s%%i/*}"; [ -z "$n" ] && n=1; d="${s##*/}"; y="$(frac "$n/$d")"; printf "0.0\t%s\n" "$y";;
    *)    printf "0.0\t0.0\n";;
  esac
}
parse_z(){  # "1/6" -> "0.166666666667\t0.0"
  r="$(frac "$1")"; printf "%s\t0.0\n" "$r"
}

# S transform for tau=i*y, z=r+ i*0
apply_S(){ # in: tr ti zr zi -> out: tr ti zr zi
  tr="$1"; ti="$2"; zr="$3"; zi="$4"
  new_tr="0.0"
  new_ti="$(awk -v y="$ti" 'BEGIN{printf("%.12f", 1.0/y)}')"
  new_zr="$(awk -v zr="$zr" -v zi="$zi" -v y="$ti" 'BEGIN{printf("%.12f", zi/y)}')"
  new_zi="$(awk -v zr="$zr" -v y="$ti" 'BEGIN{printf("%.12f", -zr/y)}')"
  printf "%s\t%s\t%s\t%s\n" "$new_tr" "$new_ti" "$new_zr" "$new_zi"
}

canon_S(){ # repeat S until Im(tau)>=1 (max 8 iters safeguard)
  tr="$1"; ti="$2"; zr="$3"; zi="$4"; cnt=0
  while awk -v y="$ti" 'BEGIN{exit !(y<1.0)}'; do
    read tr ti zr zi <<EOS
$(apply_S "$tr" "$ti" "$zr" "$zi")
EOS
    cnt=$((cnt+1)); [ "$cnt" -gt 8 ] && break
  done
  printf "%s\t%s\t%s\t%s\n" "$tr" "$ti" "$zr" "$zi"
}

canon_T(){ # drop Re(tau) mod 1 (here it's 0 or an int anyway)
  tr="$1"; ti="$2"; zr="$3"; zi="$4"
  printf "0.0\t%s\t%s\t%s\n" "$ti" "$zr" "$zi"
}

make_leaf(){ # serialize + hash
  tr="$1"; ti="$2"; zr="$3"; zi="$4"; sd="$5"
  pl="$(tau_serialize "v=1" "chart=modcanon" "tau_re=${tr}" "tau_im=${ti}" "z_re=${zr}" "z_im=${zi}" "seed=${sd}")"
  tau_sha256_str "$pl"
}

gen_set(){ # mode=S|T; arg2=k for T; arg3=seed ; prints path to tmp leaves file
  mode="$1"; tk="${2:-0}"; sd="$3"
  tmp="$(mktemp)"; : > "$tmp"
  for t in "${TAU_POINTS[@]}"; do
    IFS=$'\t' read -r tr ti <<<"$(parse_tau "$t")"
    for z in "${Z_POINTS[@]}"; do
      IFS=$'\t' read -r zr zi <<<"$(parse_z "$z")"
      # transform
      if [ "$mode" = "S" ]; then
        read tr ti zr zi <<EOS
$(apply_S "$tr" "$ti" "$zr" "$zi")
EOS
      elif [ "$mode" = "T" ]; then
        tr="$(awk -v k="$tk" 'BEGIN{printf("%.12f", k+0.0)}')"
      fi
      # canonicalize
      if [ "$mode" = "S" ]; then
        read tr ti zr zi <<EOS
$(canon_S "$tr" "$ti" "$zr" "$zi")
EOS
      else
        read tr ti zr zi <<EOS
$(canon_T "$tr" "$ti" "$zr" "$zi")
EOS
      fi
      make_leaf "$tr" "$ti" "$zr" "$zi" "$sd" >> "$tmp"
    done
  done
  printf '%s\n' "$tmp"
}

# Build canonical sets for original vs transformed
case "$XFORM" in
  S)
    A="$(gen_set S 0 "$SEED")"
    B="$(gen_set S 0 "$SEED")"
    ;;
  T:*)
    TK="${XFORM#T:}"
    A="$(gen_set T 0   "$SEED")"
    B="$(gen_set T "$TK" "$SEED")"
    ;;
  *)
    echo "[ERROR] Unknown transform. Use S or T:<k>" >&2; exit 1;;
esac

rootA="$(tau_merkle_root "$A")"
rootB="$(tau_merkle_root "$B")"
rm -f "$A" "$B"

printf "[INFO] root(original, canon)  = %s\n" "$rootA"
printf "[INFO] root(transformed, canon)= %s\n" "$rootB"

# For our grid (pure-imag τ, real z): phase(Jacobi) under S/T is zero → equality expected
if [ "$rootA" = "$rootB" ]; then
  echo "[OK] Modular-canon equality holds."
  exit 0
else
  echo "[ERROR] Roots differ." >&2
  exit 2
fi
