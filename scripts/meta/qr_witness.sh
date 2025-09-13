#!/usr/bin/env bash
# qr_witness.sh — zero‑dep, deterministic SVG hash‑QR badge + manifest stamp
set -Eeuo pipefail; set +H; umask 022
pick_latest() { pat="$1"; f=$(ls -1 $pat 2>/dev/null | LC_ALL=C sort | tail -1 || true); [ -n "$f" ] && printf "%s" "$f" || true; }
WITNESS="${1:-}"
if [ -z "$WITNESS" ]; then WITNESS="$(pick_latest .tau_ledger/sheaf/sheafv1-*.json)"; fi
if [ -z "$WITNESS" ]; then WITNESS="$(pick_latest .tau_ledger/entropy/entv1-*.json)"; fi
if [ -z "$WITNESS" ]; then WITNESS="$(pick_latest .tau_ledger/receipts/*.json)"; fi
OUT="${2:-.tau_ledger/qr/qr-witness.svg}"
if [ -z "${WITNESS:-}" ] || [ ! -s "$WITNESS" ]; then
  if [ -s .tau_ledger/CHAIN ]; then
    mkdir -p .tau_ledger/qr; WITNESS=".tau_ledger/qr/chain-witness.json"
    CHSHA=$( (command -v sha256sum >/dev/null && sha256sum .tau_ledger/CHAIN | cut -d" " -f1) || (command -v shasum >/dev/null && shasum -a 256 .tau_ledger/CHAIN | cut -d" " -f1) || (openssl dgst -sha256 .tau_ledger/CHAIN | awk "{print \$2}") )
    : > "$WITNESS"; printf "%s\n" "{" >> "$WITNESS"
    printf "%s\n" "\"schema\":\"taucrystal/chain_witness/v1\"," >> "$WITNESS"
    printf "%s\n" "\"utc\":\"$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)\"," >> "$WITNESS"
    printf "%s\n" "\"chain_sha256\":\"$CHSHA\"" >> "$WITNESS"
    printf "%s\n" "}" >> "$WITNESS"
  else
    echo "[ERR] witness not found"; exit 1
  fi
fi
sha() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d" " -f1; return; fi; if command -v shasum >/dev/null 2>&1; then shasum -a 256 "$1" | cut -d" " -f1; return; fi; openssl dgst -sha256 "$1" | awk "{print \$2}"; }
HASH="$(sha "$WITNESS")"

SVG="$OUT"; : > "$SVG"
size=21; m=8; W=$((size*m)); H=$W
printf "<svg xmlns=\\"http://www.w3.org/2000/svg\\" width=\\"$W\\" height=\\"$H\\" shape-rendering=\\"crispEdges\\">\\n" >> "$SVG"
printf "<rect width=\\"100%%\\" height=\\"100%%\\" fill=\\"#fff\\"/>\\n" >> "$SVG"
draw_finder(){ ox=$1; oy=$2; printf "<rect x=\\"%s\\" y=\\"%s\\" width=\\"%s\\" height=\\"%s\\" fill=\\"#000\\"/>\\n" $ox $oy $((7*m)) $((7*m)) >> "$SVG"; printf "<rect x=\\"%s\\" y=\\"%s\\" width=\\"%s\\" height=\\"%s\\" fill=\\"#fff\\"/>\\n" $((ox+m)) $((oy+m)) $((5*m)) $((5*m)) >> "$SVG"; printf "<rect x=\\"%s\\" y=\\"%s\\" width=\\"%s\\" height=\\"%s\\" fill=\\"#000\\"/>\\n" $((ox+2*m)) $((oy+2*m)) $((3*m)) $((3*m)) >> "$SVG"; }
draw_finder 0 0; draw_finder $(((size-7)*m)) 0; draw_finder 0 $(((size-7)*m))
hex="$HASH$HASH$HASH$HASH"; bitstr=""; for ((i=0;i<${#hex};i++)); do ch="${hex:i:1}"; case "$ch" in [0-9]) val=$((10#$ch));; a) val=10;; b) val=11;; c) val=12;; d) val=13;; e) val=14;; f) val=15;; esac; for b in 8 4 2 1; do [ $((val & b)) -ne 0 ] && bitstr="${bitstr}1" || bitstr="${bitstr}0"; done; done
idx=0; in_f(){ x=$1; y=$2; { [ $x -lt 7 ] && [ $y -lt 7 ]; } && return 0; { [ $x -ge $((size-7)) ] && [ $y -lt 7 ]; } && return 0; { [ $x -lt 7 ] && [ $y -ge $((size-7)) ]; } && return 0; return 1; }
for ((y=0;y<size;y++)); do for ((x=0;x<size;x++)); do in_f $x $y && continue; (( idx>=${#bitstr} )) && idx=0; bit=${bitstr:idx:1}; idx=$((idx+1)); [ "$bit" = "1" ] || continue; printf "<rect x=\\"%s\\" y=\\"%s\\" width=\\"%s\\" height=\\"%s\\" fill=\\"#000\\"/>\\n" $((x*m)) $((y*m)) $m $m >> "$SVG"; done; done
printf "<title>sha256:$HASH</title></svg>\\n" >> "$SVG"
man="docs/manifest.md"; tmpm="docs/.manifest.qr.$$"; : > "$tmpm"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## qr_witness (v1)"*) break ;; *) printf "%s\\n" "$line" >> "$tmpm" ;; esac; done < "$man"
printf "%s\\n\\n" "## qr_witness (v1)" >> "$tmpm"
printf "%s\\n" "witness_path: $WITNESS" >> "$tmpm"
printf "%s\\n" "witness_sha256: $HASH" >> "$tmpm"
printf "%s\\n\\n" "svg_path: $SVG" >> "$tmpm"
mv "$tmpm" "$man"
echo "[OK] qr_witness badge → $SVG (sha256:$HASH)"
