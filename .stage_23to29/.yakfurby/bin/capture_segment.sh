#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
. ".yakfurby/bin/helpers.sh"; load_cfg
SEG_ID="${1:?usage: capture_segment.sh <seg_id>}"; OUTDIR=".yakfurby/run/$SEG_ID"; mkdir -p "$OUTDIR"
V="$OUTDIR/video.h264"; A="$OUTDIR/audio.wav"; T0=$(date -u +%Y-%m-%dT%H:%M:%SZ)
if have libcamera-vid; then timeout "$CHUNK_SECONDS" libcamera-vid -t "$((CHUNK_SECONDS*1000))" -n --width "$VIDEO_WIDTH" --height "$VIDEO_HEIGHT" --framerate "$VIDEO_FPS" -o "$V" || true; else : > "$V"; printf "placeholder video %s\n" "$SEG_ID" >> "$V"; fi
if have arecord; then timeout "$CHUNK_SECONDS" arecord -f S16_LE -r "$AUDIO_RATE" -d "$CHUNK_SECONDS" "$A" || true; else : > "$A"; printf "placeholder audio %s\n" "$SEG_ID" >> "$A"; fi
T1=$(date -u +%Y-%m-%dT%H:%M:%SZ); printf "%s\n" "$T0" > "$OUTDIR/ts_start.txt"; printf "%s\n" "$T1" > "$OUTDIR/ts_end.txt"; printf "%s\n" "$SEG_ID" > "$OUTDIR/seg_id.txt"; log "captured seg=$SEG_ID from $T0 to $T1"
. ".yakfurby/bin/helpers.sh" >/dev/null 2>&1 || true
.yakfurby/bin/sense_env.sh "$SEG_ID" || true
