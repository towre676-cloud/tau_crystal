#!/usr/bin/env bash
# lines: 90
# Zero-dep, deterministic hash badge (QR-styled) + manifest stamp.
set -Eeuo pipefail; set +H; umask 022
pick(){ ls -1 $1 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
WITNESS="${1:-}"
[ -z "$WITNESS" ] && WITNESS="$(pick .tau_ledger/entropy/entv1-*.json)"
[ -z "$WITNESS" ] && WITNESS="$(pick .tau_ledger/sheaf/sheafv1-*.json)"
[ -s "${WITNESS:-}" ] || { echo "[ERR] witness not found" >&2; exit 2; }
OUT="${2:-.tau_ledger/qr/qr-witness.svg}"
mkdir -p "$(dirname "$OUT")"
sha(){ scripts/meta/_sha256.sh "$1"; }
HASH="$(sha "$WITNESS")"

# params
size=21; m=8; W=$((size*m)); H=$W
SVG="$OUT"; : > "$SVG"
printf '<svg xmlns="http://www.w3.org/2000/svg" width="%s" height="%s" shape-rendering="crispEdges">\n' "$W" "$H" >> "$SVG"
printf '<rect width="100%%" height="100%%" fill="#fff"/>\n' >> "$SVG"

draw_finder(){ ox=$1; oy=$2
  printf '<rect x="%s" y="%s" width="%s" height="%s" fill="#000"/>\n' $ox $oy $((7*m)) $((7*m)) >> "$SVG"
  printf '<rect x="%s" y="%s" width="%s" height="%s" fill="#fff"/>\n' $((ox+m)) $((oy+m)) $((5*m)) $((5*m)) >> "$SVG"
  printf '<rect x="%s" y="%s" width="%s" height="%s" fill="#000"/>\n' $((ox+2*m)) $((oy+2*m)) $((3*m)) $((3*m)) >> "$SVG"
}
draw_finder 0 0
draw_finder $(((size-7)*m)) 0
draw_finder 0 $(((size-7)*m))

# expand HASH → bitstream
hex="${HASH}${HASH}${HASH}${HASH}"
bitstr=""
for ((i=0;i<${#hex};i++)); do
  ch="${hex:i:1}"
  case "$ch" in
    [0-9]) val=$((10#$ch));;
    a) val=10;; b) val=11;; c) val=12;; d) val=13;; e) val=14;; f) val=15;;
  esac
  for b in 8 4 2 1; do
    if [ $((val & b)) -ne 0 ]; then bitstr="${bitstr}1"; else bitstr="${bitstr}0"; fi
  done
done

in_finder(){ x=$1; y=$2
  if (( x<7 && y<7 )); then return 0; fi
  if (( x>=size-7 && y<7 )); then return 0; fi
  if (( x<7 && y>=size-7 )); then return 0; fi
  return 1
}

idx=0
for ((y=0;y<size;y++)); do
  for ((x=0;x<size;x++)); do
    in_finder $x $y && continue
    (( idx>=${#bitstr} )) && idx=0
    bit=${bitstr:idx:1}; idx=$((idx+1))
    [ "$bit" = "1" ] || continue
    printf '<rect x="%s" y="%s" width="%s" height="%s" fill="#000"/>\n' $((x*m)) $((y*m)) $m $m >> "$SVG"
  done
done
printf '<title>sha256:%s</title></svg>\n' "$HASH" >> "$SVG"

# manifest section
man="docs/manifest.md"; tmp="docs/.manifest.qr.$$"; : > "$tmp"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do
  case "$line" in "## qr_witness (v1)"*) break ;; *) printf '%s\n' "$line" >> "$tmp" ;; esac
done < "$man"
{
  printf '## qr_witness (v1)\n\n'
  printf 'witness_path: %s\n' "$WITNESS"
  printf 'witness_sha256: %s\n' "$HASH"
  printf 'svg_path: %s\n\n' "$SVG"
} >> "$tmp"
mv "$tmp" "$man"
echo "[OK] qr_witness badge → $SVG (sha256:$HASH)"
