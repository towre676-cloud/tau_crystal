#!/usr/bin/env bash
set -E -o pipefail; set +H; umask 022
fr="$1"; lf="$2"; rt="$3"; t1="$4"; t2="$5"
[ -f "$fr" ] && [ -f "$lf" ] && [ -f "$rt" ] || { echo "usage: $0 <frontal> <left> <right> [FACE.txt] [face2.txt]"; exit 2; }
[ -n "${MORPHO_PASSPHRASE:-}" ] || { echo "[secure] export MORPHO_PASSPHRASE first"; exit 7; }
mkdir -p analysis/morpho/input analysis/morpho/ledger analysis/morpho/thumbs .secrets
cp -f "$fr" analysis/morpho/input/frontal.jpg
cp -f "$lf" analysis/morpho/input/left.jpg
cp -f "$rt" analysis/morpho/input/right.jpg
[ -f "$t1" ] && cp -f "$t1" analysis/morpho/input/FACE.txt  || true
[ -f "$t2" ] && cp -f "$t2" analysis/morpho/input/face2.txt || true
sha(){ openssl dgst -sha256 "$1" | awk "{print \$2}"; }
ts="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
FS="$(sha analysis/morpho/input/frontal.jpg)"; LS="$(sha analysis/morpho/input/left.jpg)"; RS="$(sha analysis/morpho/input/right.jpg)"
T1=""; T2=""; [ -f analysis/morpho/input/FACE.txt ] && T1="$(sha analysis/morpho/input/FACE.txt)"; [ -f analysis/morpho/input/face2.txt ] && T2="$(sha analysis/morpho/input/face2.txt)"
if command -v magick >/dev/null 2>&1; then
  magick analysis/morpho/input/frontal.jpg -resize 640x640 -blur 0x2 analysis/morpho/thumbs/frontal_thumb.jpg 2>/dev/null || true
  magick analysis/morpho/input/left.jpg    -resize 640x640 -blur 0x2 analysis/morpho/thumbs/left_thumb.jpg    2>/dev/null || true
  magick analysis/morpho/input/right.jpg   -resize 640x640 -blur 0x2 analysis/morpho/thumbs/right_thumb.jpg   2>/dev/null || true
fi
M=analysis/morpho/ledger/stage_manifest.tsv; : > "$M"; printf "timestamp\tfrontal_sha256\tleft_sha256\tright_sha256\tface_txt_sha\tface2_txt_sha\n" >> "$M"
printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$ts" "$FS" "$LS" "$RS" "$T1" "$T2" >> "$M"
raw=".secrets/morpho_raw_$(date -u +%Y%m%d_%H%M%S).tar"; enc="$raw.enc"
tar -cf "$raw" -C analysis/morpho/input . || { echo "[secure] tar failed"; exit 4; }
RAW_SHA="$(sha "$raw")"; openssl enc -aes-256-cbc -salt -pbkdf2 -iter 200000 -in "$raw" -out "$enc" -pass env:MORPHO_PASSPHRASE || { echo "[secure] encrypt failed"; exit 5; }
ENC_SHA="$(sha "$enc")"; RAW_SZ="$(wc -c < "$raw" 2>/dev/null || echo 0)"; ENC_SZ="$(wc -c < "$enc" 2>/dev/null || echo 0)"
L=analysis/morpho/ledger/morpho_receipts.jsonl; [ -f "$L" ] || : > "$L"
printf "{" >> "$L"; printf "\"timestamp\":\"%s\",\"frontal_sha256\":\"%s\",\"left_sha256\":\"%s\",\"right_sha256\":\"%s\"," "$ts" "$FS" "$LS" "$RS" >> "$L"
[ -n "$T1" ] && printf "\"face_txt_sha256\":\"%s\"," "$T1" >> "$L" || true
[ -n "$T2" ] && printf "\"face2_txt_sha256\":\"%s\"," "$T2" >> "$L" || true
printf "\"raw_tar\":\"%s\",\"raw_tar_sha256\":\"%s\",\"enc_file\":\"%s\",\"enc_sha256\":\"%s\",\"size_raw\":%s,\"size_enc\":%s}\n" "$(basename "$raw")" "$RAW_SHA" "$(basename "$enc")" "$ENC_SHA" "$RAW_SZ" "$ENC_SZ" >> "$L"
CS=analysis/morpho/ledger/coin_source.txt; CI=analysis/morpho/ledger/coin_id.txt; : > "$CS"
printf "%s\n%s\n%s\n%s\n%s\n" "$ts" "$FS" "$LS" "$RS" "$ENC_SHA" >> "$CS"
COIN="$(openssl dgst -sha256 "$CS" | awk "{print \$2}")"; printf "%s\n" "$COIN" > "$CI"
rm -f "$raw" 2>/dev/null || true
echo "[coin] $COIN"; echo "[ledger] $L"; echo "[enc] $enc (sha256=$ENC_SHA)"
