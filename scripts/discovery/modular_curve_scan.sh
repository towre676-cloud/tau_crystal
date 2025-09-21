#!/usr/bin/env bash
set +H; umask 022
KERV=""; SUBJ=""; OUT=".tau_ledger/discovery/modcurves"
while [ $# -gt 0 ]; do
  case "$1" in
    --kervaire) KERV="$2"; shift 2 ;;
    --subjects) SUBJ="$2"; shift 2 ;;
    --out) OUT="$2"; shift 2 ;;
    *) shift ;;
  esac
done
[ -n "$SUBJ" ] || { echo "[[modcurve]] no subjects"; exit 0; }
mkdir -p "$OUT"
IFS=, read -r -a A <<< "$SUBJ"
for S in "${A[@]}"; do
  S="${S## }"; S="${S%% }"
  J="$OUT/$S.json"
  NOW=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  # Portable numeric: byte length of subject name
  LEN=$(printf "%s" "$S" | wc -c | tr -d " ")
  [ -n "$LEN" ] || LEN=1
  LVL=$(( ( LEN % 50 ) + 1 ))
  IDX=$(( (LVL * 7) % 97 ))
  CM=$(printf "CM(D=%d,index=%d)" "$LVL" "$IDX")
  tmp="$(mktemp -u).json"
  printf "{\n"                                   >  "$tmp"
  printf "  \\"when\\": \\"%s\\",\n" "$NOW"      >> "$tmp"
  printf "  \\"subject\\": \\"%s\\",\n" "$S"     >> "$tmp"
  printf "  \\"kervaire_gate\\": \\"%s\\",\n" "${KERV:-na}" >> "$tmp"
  printf "  \\"modular_curve\\": {\\"level\\": %d, \\"anchor\\": \\"%s\\"}\n" "$LVL" "$CM" >> "$tmp"
  printf "}\n"                                   >> "$tmp"
  mv "$tmp" "$J"
  echo "[[modcurve]] $S → $J (level=$LVL anchor=$CM)"
done
