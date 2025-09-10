#!/usr/bin/env bash
set -Eeuo pipefail; set +H
L="${1:-lakefile.lean}"
[ -s "$L" ] || { echo "[err] not found: $L" >&2; exit 2; }
B="$L.bak.dups.$(date -u +%Y%m%d-%H%M%S)"; cp -f -- "$L" "$B"
awk 'BEGIN{pkg=0;tc=0;rc=0;exe=0}                                          \
{line=$0;                                                                               \
  if ($0 ~ /^[[:space:]]*package[[:space:]]+/) {                                        \
    pkg++; if (pkg>1) {print "-- DUPREMOVED package"; next}                             \
  }                                                                                     \
  if ($0 ~ /^[[:space:]]*lean_lib[[:space:]]+TauCrystal([[:space:]]|$)/) {              \
    tc++; if (tc>1) {print "-- DUPREMOVED lean_lib TauCrystal"; next}                   \
  }                                                                                     \
  if ($0 ~ /^[[:space:]]*lean_lib[[:space:]]+Receipt([[:space:]]|$)/) {                 \
    rc++; if (rc>1) {print "-- DUPREMOVED lean_lib Receipt"; next}                      \
  }                                                                                     \
  if ($0 ~ /^[[:space:]]*lean_exe[[:space:]]+/) {                                       \
    exe++; if (exe>1) {print "-- DUPREMOVED extra lean_exe"; next}                      \
  }                                                                                     \
  print line                                                                            \
}' "$B" > "$L.tmp" && mv -f "$L.tmp" "$L"
echo "[fix] wrote deduped lakefile.lean (backup: $B)"
