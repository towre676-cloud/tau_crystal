# MOTH — Historical resurrection ledger

This is an evidence-aware reconstruction of project requirements. It is **not** a recovered verbatim export of the old chats. The source chat content available to this build consisted of retrievable message fragments and a previous Soft Signal Site source file. The old GitHub repository provided a limited number of historical receipts and filenames; it did not establish that the complete historical `~/.yakfurby` software or actuator firmware was still available.

## A. March 1–3, 2025 — Persistent physical companionship

**Recovered requirements:** Raspberry Pi Zero W, BLE companion app, touch sensing, microphone/speaker, locally processed behavioral routines, persistent multi-scale memory, optional TensorFlow Lite and more ambitious VAE/HRNN memory experiments. Proposed speculative mass-fleet mathematics are not presented as implemented AI.

**Resurrection:** All state is saved as plain JSON on the user's PC; explicitly authored memories and conversation history persist across restarts. A whimsical companion avatar reacts to touch and conversation; speech synthesis uses the operating system/browser. Optional user-run Ollama allows truly generative conversation without shipping a remote-account dependency. **Absent:** embedded local neural model, always-on real-world sensory inference, full contextual semantic memory, camera/touch hardware integration.

## B. September 24–26, 2025 — Raw source-capture provenance

**User's central requirement:** a phone can pass already altered data to a signing app. Independently capture and sign the *original* audio/video stream on a Pi/microcontroller as close to the sensors as possible; distinguish capture provenance from browser-attested bytes. Historical `.yakfurby` Bash prototype reportedly supported `capture_segment.sh`, `seal_segment.sh`, `sign_digest.sh`, `provision_keys.sh`, `smoke.sh`, `peek_ledger.sh`, and `run_node.sh`. A 2025 manifest included `capsule_id`, `node_id`, `ts_start`, `ts_end`, `video_sha256`, `audio_sha256`, `combined_sha256`, and `signature_provenance`; fallback signing included software Ed25519 / SSH keys.

**Verified historical repo evidence:** `towre676-cloud/tau_crystal/analysis/capsules/test_20250925T225801Z_yakfurby-001_0.json` contains hash and provenance fields, but its recorded JSON has malformed doubled quote prefixes (`""node_id"`) and is **not** accepted as a modern cryptographic receipt. A second test manifest exists dated 2025-09-25T22:13:23Z. Source files in GitHub include `scripts/capsule/seal_capsule.sh` and demo capsule receipts from September 24, 2025. These facts do not prove hardware capture succeeded.

**Resurrection:** `hardware/pi/capture_and_witness.sh` launches Pi-local camera (`rpicam-vid` or `libcamera-vid`) and microphone (`arecord`) recording, then calls `moth-witness` Linux arm64 acquisition-node utility, which hashes actual local media files and creates `moth-witness/v1` Ed25519 signatures with a prior-envelope chain pointer. Windows companion verifies signed metadata and allows explicit trust of a device fingerprint after out-of-band checking. **Important scope:** The Bash capture launcher is tested with fake camera/microphone executables and real signing, not physically on a Pi. The Pi camera generates H.264 video after firmware/ISP processing, not unprocessed CMOS sensor bits. Importing only a manifest verifies the signed statement, NOT media bytes. The Pi utility can verify media bytes when given the local file. None of this attests secure boot, a tamper-proof sensor path, trusted timestamp, or a TPM-backed non-exportable signing key. A compromised Pi can lie. Those controls remain future hardware work.

## C. January 10–11, 2026 — Cheap actuators and distributed physical fleet

**Recovered explicit user preference:** inexpensive embodied toys and self-learning **edge AI**, not merely a toy swarm. The estimated $14 Pi/servo cost was an aspirational concept, not a verified bill of materials. The user asked about 1,000 units communicating en masse after asking for real, affordable motion.

**Recovered architecture:** `ActuationHAL`, `SensingHAL`, `PrimitiveLibrary`, `Normalizer`, `TransportModel`, `LoopExecutor`, `PersistenceFilter`, `CoherenceManager`, `RealTimeSupervisor`, `FactoryCal`. Suggested Pi Zero 2 W with RP2040/PCA9685 and physical fleet of ~1,000 units, clustered 20–50. Audio was intended for timing/event sensing; IR for short-range neighbor handshake; BLE for roles/identities; Wi-Fi for large transfers. Targets of approximately ±20–30 ms beat alignment and ±2° neutral were **proposals**, not lab results.

**Resurrection:** Windows app has Web Serial live send and response reader (Edge/Chrome), an Arduino/compatible microcontroller firmware example, bounded head/ear movement, conservative easing and watchdog neutral. Real servo motion is not a simulation, but servo position is OPEN LOOP. The +20 ms/±2° metrics are unverified. **Absent:** mass-mesh transport, per-unit calibration, real position sensors, closed-loop normalization, measured accuracy and stability under battery voltage changes, physical multi-node synchronization.

## D. November 18, 2026 — The earlier Soft Signal page

The Library contained `Soft Signal Connected Furby Workbench.txt`, describing a “Moth” mascot, memory shelf, rhythm game, 96 seeded simulated nodes, browser-signed capsules and a Raspberry Pi verifier link at `https://soft-signal-furby-lab.towre676.chatgpt.site/softsignal-pi.py`. That architecture was criticized because it did not solve the independent raw-stream capture or physical actuator synchronization problem. This resurrection discards the decorative simulated swarm as a proxy for real hardware.

## Verification checklist

- [x] Native Windows amd64 PE executable compiled from Go source (runs a local HTTP server and opens a dedicated Edge app-style window; an installed Edge is needed for the chromeless view)
- [x] No account needed to start; all new state under the user's application config directory
- [x] Conversation history, intentional memories, basic offline response engine, opt-in Ollama local LLM
- [x] Avatar touch, mood and energy, browser speech synthesis, opt-in browser speech recognition warning
- [x] Web Serial control path plus conservative Arduino servo firmware (automated JS/Go tests only, physical testing still needed)
- [x] Local Ed25519-signed hash-chain of recorded events and tamper test
- [x] Raspberry Pi arm64 signer/verifier, direct-camera/microphone Bash acquisition wrapper with fixture test, and real altered-media detection
- [ ] Independent trusted capture requires a verified secure hardware/sensor acquisition chain (**not implemented**)
- [ ] Install and field-test Windows executable on actual Windows 11 device
- [ ] Test Arduino board, actual motion and mechanical calibration with safely powered servos
- [ ] Field-test Pi camera/microphone capture, hardware custody and trust exchange
- [ ] Port/verify legacy Bash, Android witness and original user-authored content beyond retrievable fragments
- [ ] Publish new dedicated public ChatGPT Sites page and host executable download on it (publishing tool not yet available)

The chat excerpts are source context, not independently auditable original transcript downloads. Changes to the app are authored afresh, not falsely presented as preserved verbatim old code.

## E. Release v0.1.1 verification upgrade — November 19, 2026

A second verification mode was added: select the physical media file after importing its signed witness envelope. The Windows companion streams the selected bytes to its loopback-only Go service (never to a cloud endpoint), recomputes the SHA-256 digest and byte length, and records a **media verified** result only on an exact match. An altered file is rejected. A trusted public key still does not establish that its device or sensor was uncompromised. The original September YakFurby public manifests remain archival evidence, not signed v1 envelopes. The Pi signer gained `-mode fingerprint` for direct on-device comparison of trust identities. Automated Go tests cover media mismatch, correct media, state persistence, and cross-site rejection. A shell fixture checks Pi source-side capture, signed envelopes, and tamper rejection with simulated camera and microphone executables. Both UI layouts are tested in offline Chromium with mocked fetch data because sandbox Chromium forbids direct localhost navigation.

The Windows GUI heartbeat now enables shutdown after a sustained absence of its application window; it cannot establish that Windows installation succeeded. The companion still requires a real Windows machine for installer and system browser QA. **The final hardware provenance problem remains an experimental security problem, not something solved by signing at the Pi:** secure boot / protected key / firmware integrity / trusted sensor path are not present.
