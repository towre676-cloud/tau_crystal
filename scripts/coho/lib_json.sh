#!/usr/bin/env bash
jstr(){ sed -n -E "s/^[[:space:]]*\"$2\"[[:space:]]*:[[:space:]]*\"([^\"]*)\".*/\1/p" "$1" | head -n1; }
jint(){ sed -n -E "s/^[[:space:]]*\"$2\"[[:space:]]*:[[:space:]]*([-]?[0-9]+).*/\1/p" "$1" | head -n1; }
TAB(){ printf "\t"; }
HAVE(){ command -v "$1" >/dev/null 2>&1; }
HASH(){ if HAVE sha256sum; then sha256sum "$1" | awk "{print \\$1}"; elif HAVE openssl; then openssl dgst -sha256 "$1" | awk "{print \\$NF}"; else echo ""; fi }
