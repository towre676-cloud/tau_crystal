#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
. ".yakfurby/bin/helpers.sh"; load_cfg
SEG_ID="${1:?usage: seal_segment.sh <seg_id>}"; SDIR=".yakfurby/run/$SEG_ID"; [ -d "$SDIR" ] || die "missing segment dir"
V="$SDIR/video.h264"; A="$SDIR/audio.wav"; TS0=$(cat "$SDIR/ts_start.txt"); TS1=$(cat "$SDIR/ts_end.txt")
HV=$(sha256_file "$V")
HA=$(sha256_file "$A")
COMBINED=$(printf "%s|%s|%s|%s" "$HV" "$HA" "$TS0" "$TS1" | sha256sum | awk "{print \$1}")
.yakfurby/bin/sign_digest.sh "$COMBINED" "$SDIR/sig.bin" "$SDIR/sign.meta"
LED="$LEDGER_DIR/chain.tsv"; touch "$LED"
PREV=$(tail -n1 "$LED" 2>/dev/null | awk -F"\t" "{print \$2}")
if [ -n "${PREV:-}" ]; then LINKED=$(printf "%s|%s" "$PREV" "$COMBINED" | sha256sum | awk "{print \$1}"); else LINKED="$COMBINED"; fi
printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$SEG_ID" "$COMBINED" "$LINKED" "$TS0" "$TS1" "$NODE_ID" >> "$LED"
TM="$CAPS_DIR/${SEG_ID}.json"; : > "$TM"
printf "{" >> "$TM"
printf '"capsule_id":"%s","' "$SEG_ID" >> "$TM"
printf '"node_id":"%s","' "$NODE_ID" >> "$TM"
printf '"ts_start":"%s","' "$TS0" >> "$TM"
printf '"ts_end":"%s","' "$TS1" >> "$TM"
printf '"video_sha256":"%s","' "$HV" >> "$TM"
printf '"audio_sha256":"%s","' "$HA" >> "$TM"
printf '"combined_sha256":"%s","' "$COMBINED" >> "$TM"
PROV=$(awk -F"=" "/provenance/{print \$2}" "$SDIR/sign.meta" | tail -n1); [ -n "${PROV:-}" ] || PROV="unknown"
printf '"signature_provenance":"%s"}\n' "$PROV" >> "$TM"
OUT="$CAPS_DIR/${SEG_ID}.cap.tar"
tar -cf "$OUT" -C "$SDIR" video.h264 audio.wav sig.bin -C "$CAPS_DIR" "${SEG_ID}.json" 2>/dev/null || tar -cf "$OUT" -C "$SDIR" video.h264 audio.wav sig.bin
SHA=$(sha256_file "$OUT")
printf "%s\n" "$SHA" > "${OUT}.sha256"
log "sealed seg=$SEG_ID sha256=$SHA link=$LINKED provenance=$PROV"
