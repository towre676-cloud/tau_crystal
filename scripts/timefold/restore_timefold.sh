#!/usr/bin/env bash
set -Eeuo pipefail; set +H
id="${1:?usage: restore_timefold.sh <tf-id|archive> [dest] }"
dest="${2:-.tau_restore}"
root=".tau_ledger/timefolds"; arc="$id"
test -f "$arc" || arc="$root/$id.tar.gz"
test -f "$arc" || { echo "[err] archive not found: $id" >&2; exit 2; }
mkdir -p "$dest"
tar -xzf "$arc" -C "$dest"
printf "%s\n" "$dest"
