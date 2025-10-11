#!/usr/bin/env bash
# WZW/CS corridor helpers in pure Bash + bc -l (for SU(2)_k)

set -euo pipefail

# --- deps check ---
if ! command -v bc >/dev/null 2>&1; then
  echo "Error: 'bc' not found. Install bc (with math lib)." >&2
  exit 1
fi
# quick check that bc -l has trig
echo 'scale=10; s(1)+c(1)' | bc -l >/dev/null 2>&1 || {
  echo "Error: 'bc -l' here lacks trig functions s(), c()." >&2
  exit 1
}

usage() {
  cat <<'EOF'
Usage:
  ./wzw_su2.sh dim  <k> <g>            # Verlinde dimension for SU(2)_k, genus g
  ./wzw_su2.sh S    <k>                # Print S-matrix (k+1)x(k+1)
  ./wzw_su2.sh T    <k>                # Print T-matrix diagonal entries (as Re + i Im)
  ./wzw_su2.sh qdim <k> <lambda>       # Quantum dimension d_lambda = S_{0λ}/S_{00}
  ./wzw_su2.sh fuse <k> <a> <b> <c>    # Fusion coefficient N_{ab}^c (0 or 1)
  ./wzw_su2.sh fuse-list <k> <a> <b>   # List all c with N_{ab}^c = 1
  ./wzw_su2.sh info                    # Notes

Examples:
  ./wzw_su2.sh dim 2 1
  ./wzw_su2.sh S 3
  ./wzw_su2.sh T 3
  ./wzw_su2.sh qdim 5 2
  ./wzw_su2.sh fuse 5 2 3 1
  ./wzw_su2.sh fuse-list 5 2 3
EOF
}

info() {
  cat <<'EOF'
This is a Bash-only tool for SU(2)_k WZW data:

- S-matrix: S_{λμ} = sqrt(2/(k+2)) * sin(π(λ+1)(μ+1)/(k+2))
- Verlinde dimension (genus g): V_k(g) = sum_λ (S_{0λ}/S_{00})^(2-2g)
- Quantum dim: d_λ = S_{0λ}/S_{00}
- Fusion rule (closed form for SU(2)_k):
  N_{ab}^c = 1 iff
    (i) |a-b| <= c <= min(a+b, 2k - a - b),
    (ii) a+b+c is even,
    (iii) 0 <= a,b,c <= k; else 0.
- T-diagonal: T_{λλ} = exp(2πi*(h_λ - c/24)),
  with h_λ = λ(λ+2)/(4(k+2)) and c = 3k/(k+2).

Anomaly note:
- For simply-connected SU(2) in this corridor: linear theory branch is OK.
EOF
}

# --- bc helpers ---
pi_expr='4*a(1)'   # π = 4 arctan(1)

round_to_int() { echo "scale=0; ($1+0.5)/1" | bc; }

# S_{λμ} for SU(2)_k
S_entry() {
  local k="$1" lam="$2" mu="$3"
  echo "scale=50;
    k=$k; lam=$lam; mu=$mu;
    factor=sqrt(2/(k+2));
    pi=$pi_expr;
    x=pi*(lam+1)*(mu+1)/(k+2);
    factor*s(x)
  " | bc -l
}

print_S_matrix() {
  local k="$1"
  for lam in $(seq 0 "$k"); do
    local row=()
    for mu in $(seq 0 "$k"); do
      row+=( "$(S_entry "$k" "$lam" "$mu")" )
    done
    printf '%s\n' "${row[*]}"
  done
}

print_T_diag() {
  local k="$1"
  echo "scale=50; k=$k; pi=$pi_expr; c=3*k/(k+2);
  for (lam=0; lam<=k; lam++) {
    h=lam*(lam+2)/(4*(k+2));
    phase=2*pi*(h - c/24);
    real=c(phase); imag=s(phase);
    print \"λ=\"; print lam; print \": \"; print real; print \" \";
    if (imag>=0) { print \"+\"; } print imag; print \"i\n\";
  }" | bc -l
}

verlinde_dim_su2() {
  local k="$1" g="$2"
  local S00 S0l e sum term
  S00="$(S_entry "$k" 0 0)"
  e=$((2-2*g))
  sum="0"
  for lam in $(seq 0 "$k"); do
    S0l="$(S_entry "$k" 0 "$lam")"
    term="$(echo "scale=50; r=($S0l)/($S00); e=$e; if (e>=0) { r^e } else { 1/(r^(-e)) }" | bc -l)"
    sum="$(echo "scale=50; $sum + $term" | bc -l)"
  done
  round_to_int "$sum"
}

qdim_su2() {
  local k="$1" lam="$2"
  local S00 S0l
  S00="$(S_entry "$k" 0 0)"
  S0l="$(S_entry "$k" 0 "$lam")"
  echo "scale=20; ($S0l)/($S00)" | bc -l
}

fusion_su2() {
  local k="$1" a="$2" b="$3" c="$4"
  if (( a<0 || b<0 || c<0 || a>k || b>k || c>k )); then echo 0; return; fi
  local abs_ab=$(( a>b ? a-b : b-a ))
  local upper=$(( (a+b) < (2*k - a - b) ? (a+b) : (2*k - a - b) ))
  if (( c < abs_ab || c > upper )); then echo 0; return; fi
  if (( (a+b+c) % 2 != 0 )); then echo 0; return; fi
  echo 1
}

fusion_list_su2() {
  local k="$1" a="$2" b="$3"
  local c first=1
  for c in $(seq 0 "$k"); do
    if [[ "$(fusion_su2 "$k" "$a" "$b" "$c")" == "1" ]]; then
      if (( first )); then printf "%d" "$c"; first=0; else printf " %d" "$c"; fi
    fi
  done
  printf "\n"
}

cmd="${1:-}"
case "$cmd" in
  dim)        [[ $# -eq 3 ]] && verlinde_dim_su2 "$2" "$3" || { usage; exit 1; } ;;
  S)          [[ $# -eq 2 ]] && print_S_matrix "$2"        || { usage; exit 1; } ;;
  T)          [[ $# -eq 2 ]] && print_T_diag "$2"          || { usage; exit 1; } ;;
  qdim)       [[ $# -eq 3 ]] && qdim_su2 "$2" "$3"         || { usage; exit 1; } ;;
  fuse)       [[ $# -eq 5 ]] && fusion_su2 "$2" "$3" "$4" "$5" || { usage; exit 1; } ;;
  fuse-list)  [[ $# -eq 4 ]] && fusion_list_su2 "$2" "$3" "$4" || { usage; exit 1; } ;;
  info|"")    info ;;
  -h|--help)  usage ;;
  *)          echo "Unknown command: $cmd" >&2; usage; exit 1 ;;
esac
