#!/usr/bin/env bash
# Repeatable acquisition pipeline test without claiming a real Pi bench test.
set -Eeuo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TEST_DIR="$(mktemp -d)"
trap 'rm -rf "$TEST_DIR"' EXIT
mkdir -p "$TEST_DIR/bin" "$TEST_DIR/captures"
cat > "$TEST_DIR/bin/rpicam-vid" <<'CAM'
#!/usr/bin/env bash
set -euo pipefail
OUT=""
while (($#)); do
  if [[ "$1" == "--output" ]]; then OUT="$2"; shift 2; else shift; fi
done
[[ -n "$OUT" ]] || exit 2
printf '%s\n' 'fixture: camera frames acquired on simulated Pi' > "$OUT"
CAM
cat > "$TEST_DIR/bin/arecord" <<'MIC'
#!/usr/bin/env bash
set -euo pipefail
OUT="${!#}"
printf '%s\n' 'fixture: raw microphone samples on simulated Pi' > "$OUT"
MIC
chmod +x "$TEST_DIR/bin/rpicam-vid" "$TEST_DIR/bin/arecord"
( cd "$ROOT" && go build -trimpath -o build/moth-witness-linux-amd64 ./cmd/witness )
export PATH="$TEST_DIR/bin:$PATH"
export MOTH_NODE_ID="moth-test-fixture"
export MOTH_CAPTURE_DIR="$TEST_DIR/captures"
export MOTH_WITNESS_BIN="$ROOT/build/moth-witness-linux-amd64"
export HOME="$TEST_DIR/home"
mkdir -p "$HOME"
"$ROOT/hardware/pi/capture_and_witness.sh" 1
DIR="$(find "$TEST_DIR/captures" -mindepth 1 -maxdepth 1 -type d | head -1)"
[[ -n "$DIR" && -s "$DIR/camera.h264" && -s "$DIR/microphone.wav" ]]
[[ -s "$DIR/camera.moth.json" && -s "$DIR/microphone.moth.json" ]]
"$MOTH_WITNESS_BIN" -mode verify -file "$DIR/camera.h264" -out "$DIR/camera.moth.json" | grep -q '"valid": true'
"$MOTH_WITNESS_BIN" -mode verify -file "$DIR/microphone.wav" -out "$DIR/microphone.moth.json" | grep -q '"valid": true'
"$MOTH_WITNESS_BIN" -mode fingerprint | grep -q 'Device public-key fingerprint:'
printf '%s\n' 'altered' >> "$DIR/camera.h264"
if "$MOTH_WITNESS_BIN" -mode verify -file "$DIR/camera.h264" -out "$DIR/camera.moth.json" >/dev/null; then
  echo 'FAIL: altered camera bytes accepted' >&2; exit 1
fi
echo 'PASS: Pi capture fixture acquired, signed, verified, and rejected tampered media.'
