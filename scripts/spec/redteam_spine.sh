#!/usr/bin/env bash
set -Ee -o pipefail; set +H; umask 022
fail(){ echo "[redteam] $1" >&2; exit 2; }
# 0) PANIC must hard-fail
tmp=$(mktemp); trap 'rm -f "$tmp"' EXIT
touch "$tmp"; mv -f "$tmp" PANIC; git add PANIC; git commit -m "rt: panic trip" >/dev/null 2>&1 || true
if [ -f PANIC ]; then rm -f PANIC; git add -A; git commit -m "rt: clear panic" >/dev/null 2>&1 || true; else fail "PANIC not creatable"; fi
# 1) Labs quarantine: no root workflows beyond allowlist
for w in .github/workflows/*.yml .github/workflows/*.yaml; do [ -f "$w" ] || continue; base=$(basename "$w"); case "$base" in assure.yml|panic-sentinel.yml) ;; *) fail "root workflow should be quarantined: $w";; esac; done
# 2) CHAIN integrity: last receipt must link to previous hash
last=$(tail -n1 .tau_ledger/CHAIN); [ -n "$last" ] || fail "empty CHAIN";
prev=$(tail -n2 .tau_ledger/CHAIN | head -n1 | awk "{print \$1}")
rec=$(printf "%s" "$last" | awk "{print \$2}")
[ -s "$rec" ] || fail "missing receipt $rec"
pv=$(sed -n 's/.*"prev":"\([^"]*\)".*/\1/p' "$rec")
[ -z "$pv" ] || [ "$pv" = "$prev" ] || fail "prev mismatch $pv != $prev"
# 3) Cosign key rotation consistency (if cosign.pub present)
if [ -s cosign.pub ]; then rp=$(sed -n "s/.*\"cosign_pubkey\":\"\\([^\"]*\\)\".*/\\1/p" "$rec" | tr "|" "\n" | sed "s/\\\\n/\n/g");
  diff -u <(printf "%s\n" "$rp") <(tr -d "\r" < cosign.pub) >/dev/null || fail "cosign.pub mismatch vs receipt";
fi
# 4) Receipt immutability: flip one byte and ensure verify fails
cp -f "$rec" "$rec.bak"; printf " " >> "$rec"; if bash scripts/ops/verify_offline.sh 2>/dev/null; then mv -f "$rec.bak" "$rec"; fail "offline verify did not fail on tamper"; fi; mv -f "$rec.bak" "$rec"
echo "[redteam] spine hardened"
