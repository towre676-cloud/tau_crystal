#!/usr/bin/env bash
# Smooth loop holonomy: Fourier series integrand + Merkle receipt
set -euo pipefail; set +H; umask 022; export LC_ALL=C
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "${SCRIPT_DIR}/dchar_lib.sh"
[ -f "${SCRIPT_DIR}/utils.sh" ] && source "${SCRIPT_DIR}/utils.sh" || true
STEPS=64; SEED="0"
while [ $# -gt 0 ]; do case "$1" in --steps) STEPS="$2"; shift 2;; --seed) SEED="$2"; shift 2;; -h|--help) echo "Usage: $0 [--steps N] [--seed S]"; exit 0;; *) echo "Unknown: $1" >&2; exit 1;; esac; done
coeff(){ key="$1"; amp="$2"; h="$(tau_sha256_str "$key")"; u="0x${h:0:8}";
  awk -v U="$u" -v A="$amp" 'BEGIN{u=strtonum(U); x=u/4294967295.0; y=2*x-1; printf("%.12f\n", A*y)}'; }
A0="$(coeff "${SEED}|a0" 0.20)"
A1="$(coeff "${SEED}|a1" 0.15)"; B1="$(coeff "${SEED}|b1" 0.15)"
A2="$(coeff "${SEED}|a2" 0.10)"; B2="$(coeff "${SEED}|b2" 0.10)"
tmp="$(mktemp)"; : > "$tmp"
phase="0.0"
for ((i=0;i<STEPS;i++)); do
  th="$(awk -v i="$i" -v n="$STEPS" 'BEGIN{pi=atan2(0,-1); printf("%.16f\n", 2*pi*i/n)}')" 
  f="$(awk -v th="$th" -v a0="$A0" -v a1="$A1" -v b1="$B1" -v a2="$A2" -v b2="$B2" 'BEGIN{f=a0+a1*cos(th)+b1*sin(th)+a2*cos(2*th)+b2*sin(2*th); printf("%.17f\n",f)}')" 
  inc="$(awk -v f="$f" -v n="$STEPS" 'BEGIN{printf("%.17f\n", f/n)}')" 
  pl="$(tau_serialize "v=1" "chart=loop_smooth" "i=${i}" "N=${STEPS}" "theta=${th}" "inc=${inc}" "seed=${SEED}")"
  h="$(tau_sha256_str "$pl")"; printf "%s\n" "$h" >> "$tmp"
  phase="$(awk -v a="$phase" -v b="$inc" 'BEGIN{s=a+b; while(s>=1)s-=1; while(s<0)s+=1; printf("%.17f\n",s)}')" 
done
root="$(tau_merkle_root "$tmp")"; rm -f "$tmp"
dir="$(tau_receipt_dir)"; rec="${dir}/loop_smooth.receipt"; : > "$rec"
printf "%s\n" "kind=loop_smooth"     >> "$rec"
printf "%s\n" "steps=${STEPS}"       >> "$rec"
printf "%s\n" "seed=${SEED}"         >> "$rec"
printf "%s\n" "phase_frac=${phase}"  >> "$rec"
printf "%s\n" "root_sha256=${root}"  >> "$rec"
log_ok "Holonomy (smooth): ${phase}"
log_ok "Merkle root: ${root}"
log_ok "Receipt: ${rec}"
