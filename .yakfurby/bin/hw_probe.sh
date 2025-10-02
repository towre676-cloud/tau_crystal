#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
say(){ printf "[%s] %s\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*"; }
ok(){ say "OK  - $*"; } ; warn(){ say "WARN- $*"; } ; fail(){ say "FAIL- $*"; exit 1; }
if command -v i2cdetect >/dev/null 2>&1; then
  MAP=$(i2cdetect -y 1 2>/dev/null || true); echo "$MAP" | grep -q "40" && ok "INA219 visible at 0x40" || warn "no device at 0x40 (adjust address or wiring)"
else warn "i2c-tools not installed"; fi
GPIO=/sys/class/gpio/gpio17/value; [ -r "$GPIO" ] && { v=$(cat "$GPIO" || echo "?"); ok "GPIO17 readable value=$v"; } || warn "GPIO17 not readable (udev not fired yet?)"
if command -v libcamera-hello >/dev/null 2>&1; then ok "libcamera installed"; else warn "libcamera not found"; fi
if command -v arecord >/dev/null 2>&1; then ok "arecord present"; else warn "alsa-utils missing"; fi
if command -v tpm2_getrandom >/dev/null 2>&1; then tpm2_getrandom 8 >/dev/null 2>&1 && ok "TPM responds" || warn "TPM tool present, device maybe absent"; else warn "tpm2-tools not installed"; fi
