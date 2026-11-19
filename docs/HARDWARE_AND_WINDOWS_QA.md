# Moth acceptance testing — Windows 11, Pi, and physical servo controller

This is a reproducible procedure to run with **actual hardware**. The release was compiled on Linux and tested without these physical devices; do not treat any fixture PASS as a physical success.

## Windows 11 runtime

- Download ZIP, inspect its SHA-256 checksum, unpack it, and start `MothCompanion.exe` on Windows 11 x64. Confirm Edge opens an app-style window and that `%APPDATA%\MothCompanion\` is created.
- Talk to Moth, save a deliberate memory, mark a task completed, export a backup, quit, restart and confirm state is retained.
- In Settings, opt in to Ollama **only after** installing the local service and a model. Check that genuine model output is labeled Ollama and the disconnected fallback is labeled offline.
- Run `powershell -NoProfile -ExecutionPolicy Bypass -File .\tests\windows_selftest.ps1` in the extracted folder from a Windows PowerShell prompt after reviewing the script. It checks the real executable's localhost API, memory/chat/task flow, signed chain and graceful exit, and writes `Moth-Windows-QA.json` alongside the script.
- Shut the Edge app window without pressing Quit, then wait a few minutes and confirm Moth's localhost process terminates (window heartbeat auto-exit); Windows sleep/resume should be tested separately.
- Confirm SmartScreen behavior and Windows Defender scans. Binary is not Authenticode-signed; do not suppress security controls indiscriminately.

## Arduino or RP2040 connected servo fixture

- Physically disconnect horns and linkage, power the servos from a current-rated **separate regulated supply** (shared ground), install firmware, connect USB, and inspect the controller greeting.
- Test head neutral, bounded ±20° nod, ear ±24° wiggle, `stop`, disconnected USB, and 5-second watchdog recovery.
- Reconnect mechanical linkage only after verifying no collisions at the configured stops. Observe heating, current draw and neutral after battery-voltage changes; log angles independently with an angle gauge or encoders.
- **Never** claim calibrated ±2° drift or closed-loop actuation from this sketch: Servo.h drives open-loop positions with no encoders and no per-device FactoryCal.

## Raspberry Pi source acquisition

- Use a Pi with a directly attached compatible camera and microphone, install `rpicam-vid`/`libcamera-vid`, `arecord`, and `moth-witness-linux-arm64`.
- Run `./moth-witness-linux-arm64 -mode fingerprint` locally; compare the fingerprint against the Windows app **without relying on the media transit channel**.
- Run `./capture_and_witness.sh 10` on the Pi. Confirm `.h264`, `.wav`, and paired `.moth.json` files actually exist, and run `-mode verify -file ... -out ...` against **both** recording files.
- Transfer each manifest and its media file to the Windows PC. Import the manifest, then select its corresponding actual video/audio file to verify byte equality. Modify a copy of the media to check that Moth explicitly rejects it.
- Reset or compromise the Pi signer key in a controlled lab environment to confirm new fingerprints are NOT implicitly trusted. Verify secure boot, hardware key isolation, acquisition firmware and trusted timestamps separately if claiming trusted original sensor evidence.

## Physical thousand-device fleet

This release has **no** validated large-fleet synchronization. A credible field campaign requires: individually calibrated actuators, independent position sensors, authenticated pair/cluster identities, BLE/IR/audio radio coexistence tests, clock alignment and drift logging, 20-node first cluster, and controlled 50-cluster scaling under loss and low battery. Proposed 20–30 ms synchronization and ±2° position targets must be measured, with p50/p95/p99 error and recovery distributions, before publication as engineering results.
