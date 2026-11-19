#!/usr/bin/env bash
# Moth source-side capture: camera and microphone run ON the Raspberry Pi.
# Requires rpicam-vid (or libcamera-vid), arecord and the moth-witness arm64 binary.
# Acquisition custody and firmware integrity must be verified separately.
set -Eeuo pipefail
umask 077
DURATION="${1:-10}"
if [[ ! "$DURATION" =~ ^[0-9]+$ ]] || (( DURATION < 1 || DURATION > 120 )); then
  printf 'Usage: %s [duration_in_seconds=10, 1..120]\n' "$0" >&2
  exit 2
fi
NODE="${MOTH_NODE_ID:-moth-pi-01}"
BASE="${MOTH_CAPTURE_DIR:-${HOME:?}/MothCaptures}"
BIN="${MOTH_WITNESS_BIN:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/moth-witness-linux-arm64}"
if [[ ! -x "$BIN" ]]; then
  echo "Missing executable source-device witness binary: $BIN" >&2; exit 2
fi
if command -v rpicam-vid >/dev/null 2>&1; then
  CAMERA="$(command -v rpicam-vid)"
elif command -v libcamera-vid >/dev/null 2>&1; then
  CAMERA="$(command -v libcamera-vid)"
else
  echo 'Camera utility rpicam-vid (or libcamera-vid) is required ON the Pi.' >&2; exit 2
fi
if ! command -v arecord >/dev/null 2>&1; then
  echo 'ALSA microphone utility arecord is required ON the Pi.' >&2; exit 2
fi
ID="$(date -u +%Y%m%dT%H%M%SZ)-$(od -An -N4 -tx1 /dev/urandom | tr -d ' \n')"
DIR="$BASE/$ID"
mkdir -p "$DIR"
VIDEO="$DIR/camera.h264"
AUDIO="$DIR/microphone.wav"
CAM_PID=''; MIC_PID=''
cleanup() {
  if [[ -n "$CAM_PID" ]] && kill -0 "$CAM_PID" 2>/dev/null; then kill "$CAM_PID" 2>/dev/null || true; fi
  if [[ -n "$MIC_PID" ]] && kill -0 "$MIC_PID" 2>/dev/null; then kill "$MIC_PID" 2>/dev/null || true; fi
}
trap cleanup EXIT INT TERM
printf 'Acquiring on Pi %s: %ss camera + mic into %s\n' "$NODE" "$DURATION" "$DIR"
"$CAMERA" --timeout "$((DURATION * 1000))" --nopreview --output "$VIDEO" >"$DIR/camera.log" 2>&1 & CAM_PID=$!
arecord -q -t wav -f S16_LE -r 48000 -c 1 -d "$DURATION" "$AUDIO" >"$DIR/microphone.log" 2>&1 & MIC_PID=$!
rc=0
wait "$CAM_PID" || rc=1
wait "$MIC_PID" || rc=1
CAM_PID=''; MIC_PID=''
if (( rc != 0 )) || [[ ! -s "$VIDEO" ]] || [[ ! -s "$AUDIO" ]]; then
  echo "Physical capture did not produce both non-empty files; inspect $DIR/*.log" >&2
  exit 1
fi
# Sign and verify BOTH files on the source device; link audio to signed video envelope.
CAM_ENV="$DIR/camera.moth.json"
AUD_ENV="$DIR/microphone.moth.json"
CAM_OUTPUT="$($BIN -file "$VIDEO" -node "$NODE" -method 'pi-camera-rpicam-h264' -source 'physical-pi-camera' -out "$CAM_ENV")"
printf '%s\n' "$CAM_OUTPUT"
PREVIOUS="$(printf '%s\n' "$CAM_OUTPUT" | awk '/^Envelope SHA256:/ {print $3}')"
if [[ ! "$PREVIOUS" =~ ^[a-f0-9]{64}$ ]]; then echo 'Failed to bind the two capture receipts' >&2; exit 1; fi
"$BIN" -file "$AUDIO" -node "$NODE" -method 'pi-alsa-microphone-wav' -source 'physical-pi-microphone' -previous "$PREVIOUS" -out "$AUD_ENV"
"$BIN" -mode verify -file "$VIDEO" -out "$CAM_ENV"
"$BIN" -mode verify -file "$AUDIO" -out "$AUD_ENV"
printf '\nCapture pair verified on this device: %s\n' "$DIR"
printf 'Import camera.moth.json and microphone.moth.json separately into Moth on Windows.\n'
printf 'IMPORTANT: hardware custody, secure boot, microphone provenance and sensor authenticity are not cryptographically attested by this script.\n'
