#!/usr/bin/env bash
# dual-path qr_witness — qrencode|python3(qrcode.svg)|fallback badge; stamps manifest
set -Eeuo pipefail; set +H; umask 022
pick_latest(){ p="$1"; ls -1 $p 2>/dev/null | LC_ALL=C sort | tail -1 2>/dev/null || true; }
sha(){ if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; elif command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1; else openssl dgst -sha256 "$1" | awk "{print \$2}"; fi; }
WITNESS="${1:-}"; OUT="${2:-.tau_ledger/qr/qr-witness.svg}"
[ -n "$WITNESS" ] || WITNESS="$(pick_latest .tau_ledger/sheaf/sheafv1-*.json)"
[ -n "$WITNESS" ] || WITNESS="$(pick_latest .tau_ledger/entropy/entv1-*.json)"
[ -n "$WITNESS" ] || WITNESS="$(pick_latest .tau_ledger/receipts/*.json)"
if [ -z "${WITNESS:-}" ] || [ ! -s "$WITNESS" ]; then
  if [ -s .tau_ledger/CHAIN ]; then
    WITNESS=".tau_ledger/qr/chain-witness.json"; CHSHA="$(sha .tau_ledger/CHAIN)"; : > "$WITNESS"
    printf "%s\n" "{" >> "$WITNESS"; printf "%s\n" "\"schema\":\"taucrystal/chain_witness/v1\"," >> "$WITNESS"
    printf "%s\n" "\"utc\":\"$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)\"," >> "$WITNESS"; printf "%s\n" "\"chain_sha256\":\"$CHSHA\"" >> "$WITNESS"; printf "%s\n" "}" >> "$WITNESS"
  else echo "[ERR] witness not found"; exit 1; fi
fi
HASH="$(sha "$WITNESS")"; mkdir -p "$(dirname "$OUT")"
if command -v qrencode >/dev/null 2>&1; then echo -n "$HASH" | qrencode -t SVG -o "$OUT" >/dev/null 2>&1 || rm -f "$OUT"; fi
if [ ! -s "$OUT" ] && command -v python3 >/dev/null 2>&1; then
  py="import sys;h=sys.argv[1];o=sys.argv[2];
import qrcode, qrcode.image.svg as svg;
img=qrcode.make(h, image_factory=svg.SvgImage);img.save(o)"
  python3 -c "$py" "$HASH" "$OUT" >/dev/null 2>&1 || rm -f "$OUT"
fi
if [ ! -s "$OUT" ]; then
  SVG="$OUT"; : > "$SVG"; size=21; m=8; W=$((size*m)); H=$W
  printf "<svg xmlns=\\"http://www.w3.org/2000/svg\\" width=\\"$W\\" height=\\"$H\\" shape-rendering=\\"crispEdges\\">\\n" >> "$SVG"
  printf "<rect width=\\"100%%\\" height=\\"100%%\\" fill=\\"#fff\\"/>\\n" >> "$SVG"
  df(){ ox=$1; oy=$2; printf "<rect x=\\"%s\\" y=\\"%s\\" width=\\"%s\\" height=\\"%s\\" fill=\\"#000\\"/>\\n" $ox $oy $((7*m)) $((7*m)) >> "$SVG"; printf "<rect x=\\"%s\\" y=\\"%s\\" width=\\"%s\\" height=\\"%s\\" fill=\\"#fff\\"/>\\n" $((ox+m)) $((oy+m)) $((5*m)) $((5*m)) >> "$SVG"; printf "<rect x=\\"%s\\" y=\\"%s\\" width=\\"%s\\" height=\\"%s\\" fill=\\"#000\\"/>\\n" $((ox+2*m)) $((oy+2*m)) $((3*m)) $((3*m)) >> "$SVG"; }
  df 0 0; df $(((size-7)*m)) 0; df 0 $(((size-7)*m))
  hex="$HASH$HASH$HASH$HASH"; bit=""; for ((i=0;i<${#hex};i++)); do ch="${hex:i:1}"; case "$ch" in [0-9]) v=$((10#$ch));; a) v=10;; b) v=11;; c) v=12;; d) v=13;; e) v=14;; f) v=15;; esac; for b in 8 4 2 1; do [ $((v & b)) -ne 0 ] && bit="${bit}1" || bit="${bit}0"; done; done
  idx=0; inF(){ x=$1; y=$2; { [ $x -lt 7 ] && [ $y -lt 7 ]; } || { [ $x -ge $((size-7)) ] && [ $y -lt 7 ]; } || { [ $x -lt 7 ] && [ $y -ge $((size-7)) ]; } || return 1; return 0; }
  for ((y=0;y<size;y++)); do for ((x=0;x<size;x++)); do inF $x $y && continue; (( idx>=${#bit} )) && idx=0; [ "${bit:idx:1}" = "1" ] || { idx=$((idx+1)); continue; }; idx=$((idx+1)); printf "<rect x=\\"%s\\" y=\\"%s\\" width=\\"%s\\" height=\\"%s\\" fill=\\"#000\\"/>\\n" $((x*m)) $((y*m)) $m $m >> "$SVG"; done; done
  printf "<title>sha256:%s</title></svg>\\n" "$HASH" >> "$SVG"
fi
man="docs/manifest.md"; tmpm="docs/.manifest.qr.$$"; : > "$tmpm"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## qr_witness (v1)"*) break ;; *) printf "%s\\n" "$line" >> "$tmpm" ;; esac; done < "$man"
printf "%s\\n\\n" "## qr_witness (v1)" >> "$tmpm"; printf "%s\\n" "witness_path: $WITNESS" >> "$tmpm"; printf "%s\\n" "witness_sha256: $HASH" >> "$tmpm"; printf "%s\\n\\n" "svg_path: $OUT" >> "$tmpm"; mv "$tmpm" "$man"
echo "[OK] qr_witness → $OUT (sha256:$HASH)";
