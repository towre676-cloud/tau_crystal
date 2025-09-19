#!/usr/bin/env bash
set -Eeuo pipefail; set +H

OUT="${1:-analysis/plots/status.svg}"
TITLE="${TITLE:-τ-Crystal L-data}"
CRIT="${CRIT:-0}"
SYM2="${SYM2:-0}"
FLAG="${FLAG:-false}"

mkdir -p "$(dirname "$OUT")"

cat > "$OUT" <<SVG
<?xml version="1.0" encoding="UTF-8"?>
<svg width="720" height="240" viewBox="0 0 720 240" xmlns="http://www.w3.org/2000/svg">
  <defs>
    <style>
      .bg { fill: #0b132b; }
      .card { fill: #1c2541; stroke: #3a506b; stroke-width: 2; rx:12; ry:12; }
      .t1 { font: 700 22px monospace; fill: #e0fbfc; }
      .t2 { font: 400 16px monospace; fill: #a9def0; }
      .ok { fill: #58d68d; }
      .no { fill: #ff6b6b; }
    </style>
  </defs>
  <rect class="bg" x="0" y="0" width="720" height="240" />
  <rect class="card" x="20" y="20" width="680" height="200" />
  <text class="t1" x="40" y="60">${TITLE}</text>
  <text class="t2" x="40" y="110">critical-line zeros (GL(2)) :</text>
  <text class="t2" x="360" y="110">${CRIT}</text>
  <text class="t2" x="40" y="140">Sym² outside-strip hits      :</text>
  <text class="t2" x="360" y="140">${SYM2}</text>
  <text class="t2" x="40" y="170">flag                         :</text>
  <text class="t2" x="360" y="170">${FLAG}</text>
  <circle cx="650" cy="60" r="8" class="${FLAG#true}?no:ok"/>
</svg>
SVG
echo "$OUT"
