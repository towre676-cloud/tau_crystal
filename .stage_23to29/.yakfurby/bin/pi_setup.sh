#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
log(){ printf "[%s] %s\n" "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$*"; }
need_root(){ [ "$(id -u)" -eq 0 ] || { echo "re-run: sudo $0"; exit 1; }; }
need_root
if command -v raspi-config >/dev/null 2>&1; then raspi-config nonint do_i2c 0 || true; fi
apt-get update -y || true
apt-get install -y --no-install-recommends libcamera-apps alsa-utils i2c-tools tpm2-tools jq xxd || true
RULE=/etc/udev/rules.d/99-yakfurby-gpio.rules
cat > "$RULE" <<EOF
SUBSYSTEM=="gpio", ACTION=="add", PROGRAM="/bin/sh -c 'echo 17 > /sys/class/gpio/export 2>/dev/null || true; echo in > /sys/class/gpio/gpio17/direction 2>/dev/null || true; chgrp -R gpio /sys/class/gpio/gpio17; chmod -R g+r /sys/class/gpio/gpio17'"
EOF
udevadm control --reload-rules && udevadm trigger || true
if [ ! -e /sys/class/gpio/gpio17/value ]; then echo 17 > /sys/class/gpio/export 2>/dev/null || true; echo in > /sys/class/gpio/gpio17/direction 2>/dev/null || true; fi
adduser "${SUDO_USER:-pi}" i2c >/dev/null 2>&1 || true
adduser "${SUDO_USER:-pi}" gpio >/dev/null 2>&1 || true
log "setup complete: I2C enabled, tools installed, GPIO17 auto-export rule in place"
