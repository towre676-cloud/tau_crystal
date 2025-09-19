#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
fr="$1"; lf="$2"; rt="$3"; out="$4"; led="analysis/morpho/ledger/morpho_receipts.jsonl"
[ -n "$fr" ] && [ -n "$lf" ] && [ -n "$rt" ] && [ -n "$out" ] || { echo "[err] usage: analyze_basic.sh frontal left right out_dir"; exit 2; }
sha(){ openssl dgst -sha256 "$1" | awk "{print \$2}"; }
sz(){ wc -c < "$1" 2>/dev/null || echo 0; }
dim(){ command -v magick >/dev/null 2>&1 && magick identify -format "%w x %h" "$1" 2>/dev/null || echo "unknown"; }
ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
FR_SHA=$(sha "$fr"); LF_SHA=$(sha "$lf"); RT_SHA=$(sha "$rt")
FR_SZ=$(sz "$fr");  LF_SZ=$(sz "$lf");  RT_SZ=$(sz "$rt")
FR_DM=$(dim "$fr");  LF_DM=$(dim "$lf");  RT_DM=$(dim "$rt")
note1="analysis/morpho/input/FACE.txt"; note2="analysis/morpho/input/face2.txt"
N1_SHA=""; N2_SHA=""; [ -f "$note1" ] && N1_SHA=$(sha "$note1"); [ -f "$note2" ] && N2_SHA=$(sha "$note2")
mkdir -p "$out"
RJ="$out/morpho_report.json"; RM="$out/morpho_report.md"
: > "$RJ"; : > "$RM"
printf "%s" "{" >> "$RJ"
printf "%s" "\"timestamp\":\"$ts\"," >> "$RJ"
printf "%s" "\"frontal\":{\"sha256\":\"$FR_SHA\",\"bytes\":$FR_SZ,\"dims\":\"$FR_DM\"}," >> "$RJ"
printf "%s" "\"left\":{\"sha256\":\"$LF_SHA\",\"bytes\":$LF_SZ,\"dims\":\"$LF_DM\"}," >> "$RJ"
printf "%s" "\"right\":{\"sha256\":\"$RT_SHA\",\"bytes\":$RT_SZ,\"dims\":\"$RT_DM\"}," >> "$RJ"
printf "%s" "\"notes\":{\"FACE.txt\":\"$N1_SHA\",\"face2.txt\":\"$N2_SHA\"}" >> "$RJ"
printf "%s\n" "}" >> "$RJ"
printf "%s\n" "# Morphometric Receipt (basic)" >> "$RM"
printf "%s\n" "- timestamp: $ts" >> "$RM"
printf "%s\n" "- frontal:  sha256=$FR_SHA  bytes=$FR_SZ  dims=$FR_DM" >> "$RM"
printf "%s\n" "- left:     sha256=$LF_SHA  bytes=$LF_SZ  dims=$LF_DM" >> "$RM"
printf "%s\n" "- right:    sha256=$RT_SHA  bytes=$RT_SZ  dims=$RT_DM" >> "$RM"
[ -n "$N1_SHA" ] && printf "%s\n" "- FACE.txt sha256=$N1_SHA" >> "$RM"
[ -n "$N2_SHA" ] && printf "%s\n" "- face2.txt sha256=$N2_SHA" >> "$RM"
printf "%s\n" "" >> "$RM"
echo "[report] $RJ"; echo "[report] $RM"
printf "%s\n" "{\"timestamp\":\"$ts\",\"frontal_sha256\":\"$FR_SHA\",\"left_sha256\":\"$LF_SHA\",\"right_sha256\":\"$RT_SHA\",\"face_txt_sha256\":\"$N1_SHA\",\"face2_txt_sha256\":\"$N2_SHA\"}" >> "$led"
exit 0
