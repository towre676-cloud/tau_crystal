#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
lab_dir="$(cd "$(dirname "$0")" && pwd -P)"
adele(){ root="${1:-.}"; for p in linux x86 windows mingw macos arm64 docker baremetal; do meta=""; case "$p" in linux) [ -f /etc/os-release ] && meta="$(. /etc/os-release; echo $ID-$VERSION_ID)";; x86) uname -m 2>/dev/null | grep -qi "x86" && meta="$(uname -m)";; windows) uname -s 2>/dev/null | grep -qi "mingw\\|msys" && meta="gitbash";; mingw) uname -s 2>/dev/null | grep -qi "mingw" && meta="$(uname -s)";; macos) uname -s 2>/dev/null | grep -qi "darwin" && meta="darwin";; arm64) uname -m 2>/dev/null | grep -qi "arm64\\|aarch64" && meta="$(uname -m)";; docker) grep -qi docker /proc/1/cgroup 2>/dev/null && meta="cgroup-docker";; baremetal) true;; esac; printf "%s\t%s\n" "$p" "$meta"; done; }
frob(){ place="${1:-global}"; u="${GITHUB_RUN_ID:-0}.${GITHUB_SHA:-0}.${RANDOM}"; ram=1; [ -n "${CI:-}" ] && ram=$((ram+1)); [ -n "${GITHUB_ACTIONS:-}" ] && ram=$((ram+1)); printf "%s\t%s\t%d\n" "$place" "$u" "$ram"; }
Lfun(){ python "$lab_dir/l_compute.py" "${1:-1}" "${2:-.tau_ledger}"; }
Rank(){ python "$lab_dir/rank_compute.py" "${1:-.tau_ledger}"; }
Hecke(){ python "$lab_dir/hecke_compute.py" "${1:-3}" "${2:-.tau_ledger}"; }
Theta(){ python "$lab_dir/theta_compute.py" "${1:-1.0}" "${2:-0.0}" "${3:-.tau_ledger}"; }
Modular(){ python "$lab_dir/modular_check.py" "${1:?n}" "${2:?dirA}" "${3:?dirB}" "${4:-1e-3}"; }
case "${1:-}" in
  adele) adele "${2:-.}";;
  frobenius|frob) frob "${2:-global}";;
  L) Lfun "${2:-1}" "${3:-.tau_ledger}";;
  rank) Rank "${2:-.tau_ledger}";;
  hecke) Hecke "${2:-3}" "${3:-.tau_ledger}";;
  theta) Theta "${2:-1.0}" "${3:-0.0}" "${4:-.tau_ledger}";;
  modular) Modular "${2:?n}" "${3:?dirA}" "${4:?dirB}" "${5:-1e-3}";;
  *) echo "usage: lab.sh adele <root> | frob [place] | L <s> <dir> | rank <dir> | hecke <n> <dir> | theta <s> <t> <dir> | modular <n> <dirA> <dirB> [tol]" >&2; exit 2;;
esac
