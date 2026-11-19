# MOTH Companion — Windows resurrection build v0.1.1

**A companion you can actually run**, with persistent local memory, conversation, mood, speech, USB motion, source-side capture receipts, and optional on-PC verification of the actual media bytes. This is the first verified engineering release candidate, not a production-certified 1,000-device fleet or a securely attested camera.

## Windows quick start

1. Unzip `MothCompanion-Windows.zip` to a folder.
2. Double-click `MothCompanion.exe` (64-bit Windows 10/11). On Windows 11, Edge should open in its frameless application window. If Edge is missing, the executable opens your default browser. An unsigned fresh executable may trigger Windows SmartScreen; inspect the downloadable source and SHA256 before choosing whether to run it.
3. Click your companion to pet it; talk in the conversation panel; enter `remember that ...` to keep deliberate memories.
4. For open-ended local language-model chat, install Ollama separately, run `ollama pull llama3.2`, and enable **Use local AI model** under Settings. Moth connects ONLY to `http://127.0.0.1:11434` when you opt in. Without Ollama, replies are basic rule-based conversation, not a hidden AI service.
5. To give Moth a physical body, install the included Arduino sketch and use Edge/Chrome **Physical body** → **Connect USB controller**. The servos must have separate appropriate power and calibrated mechanical end stops. Motion is open-loop; use cautiously.
6. To witness physical source capture, put `moth-witness-linux-arm64` and `hardware/pi/capture_and_witness.sh` on the Raspberry Pi and run the script there. It invokes Pi-local camera and microphone utilities, checks both files and signs both on that device. Import each resulting `.moth.json` into **Witness archive**, then select its matching actual media file to rehash and check the bytes against the signed envelope. Confirm the fingerprint on the Pi before trusting the signing key. A signed file is NOT hardware attestation.

## Private data

Application state, event chain and local identity key are written under `%APPDATA%\MothCompanion\` (or the OS's standard user config directory). They are plain JSON and local files, not encrypted at rest. Protect Windows account access. No analytics, no remote login, no cloud storage, no hidden LAN port or remote font requests. Browser speech recognition and optional local-model service are the only network-capable integrations enabled through separate controls. Browser microphone speech recognition may use an online service: it is opt-in and displays a warning. Voice output uses installed browser/system voices when available. The app launches a random **127.0.0.1-only** local server; closing the app-style browser window does not always terminate the executable, so use Settings → **Quit Moth application**.

## Raspberry Pi witness commands

Acquire a real file on the Pi using your approved sensor toolchain, then run:

```
chmod +x moth-witness-linux-arm64
./moth-witness-linux-arm64 -file raw-capture.wav -node moth-pi-01 -method direct-on-device -out raw-capture.moth.json
./moth-witness-linux-arm64 -mode verify -file raw-capture.wav -out raw-capture.moth.json
```

Run `./moth-witness-linux-arm64 -mode fingerprint` on the Pi to display the device key fingerprint without signing a file. The executable makes a local Ed25519 key if none exists in `~/.moth-witness/device.ed25519`. To link a subsequent capture's envelope to its predecessor, supply the predecessor envelope SHA256 using `-previous`. Do not circulate private signing keys. A microcontroller or protected key store is required to improve resistance against source/device compromise.

## Direct recording on the Raspberry Pi

With a supported physical Pi camera, USB/ALSA microphone, Raspberry Pi OS `rpicam-vid` (or `libcamera-vid`) and `arecord` already installed, put both release files in the same directory on the Pi, then run:

```
chmod +x moth-witness-linux-arm64 capture_and_witness.sh
./capture_and_witness.sh 10
```

This starts a 10-second physical Pi-local camera and microphone capture concurrently. The files are recorded locally, separately signed with a persistent Ed25519 key, and then independently rehashed and checked on the source device. The two signed envelope statements are chained. No phone sends the footage to the capture script. The camera path emits H.264 processed by Pi firmware/ISP; this is not raw CMOS sensor output, tamper-resistant hardware attestation, or verified trustworthy sensor firmware. The wrapper was tested with stub capture utilities and the real witness signer, NOT with a real Pi camera or mic yet.

## Source and tests

Go 1.23+; no third-party Go dependencies. The UI HTML/CSS/JS is embedded in the executable.

```
go test ./...
GOOS=windows GOARCH=amd64 CGO_ENABLED=0 go build -ldflags="-H=windowsgui" -o MothCompanion.exe ./cmd/moth
GOOS=linux GOARCH=arm64 CGO_ENABLED=0 go build -o moth-witness-linux-arm64 ./cmd/witness
```

Use `MothCompanion.exe --no-browser --port 7777 --data-dir C:\\Temp\\MothTest` for debugging with browser at `http://127.0.0.1:7777`.

## Provenance & known limits

Read `docs/RESURRECTION_LEDGER.md` for the detailed distinction between March/September 2025 and January 2026 chat requirements, actual GitHub evidence, and the code implemented in this release. The Windows GUI is an Edge application-mode webview launched by a compiled self-contained Go executable, **not** a native WinUI or WebView2 embedded window. The compiled Windows binary has been statically inspected but cannot be executed on a Windows computer in the Linux build environment. Run `tests/windows_selftest.ps1` on the target machine to generate a local launch-and-API validation receipt. A public ChatGPT Sites download page is staged but not yet published.

Moth is an independent prototype inspired by the user's connected-plush concept. “Furby” is a trademark of its respective owner; this is not an official Furby product.

## Release verification

`go test -race ./...`, `go vet ./...`, `tests/pi_capture_fixture.sh`, and `python tests/visual_smoke.py` check core flows, Pi emulated acquisition, and desktop/mobile responsive rendering. The visual test is a browser mock, not actual PC window validation. See `docs/HARDWARE_AND_WINDOWS_QA.md` for instructions and explicit physical-test acceptance criteria.
