#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
rep=".tau_ledger/gates/report.$(date -u +%Y%m%dT%H%M%SZ).txt"; : > "$rep"
ok=0; fail=0
[ -x scripts/timefold/verify_timefold.sh ] && { if scripts/timefold/verify_timefold.sh >>"$rep" 2>&1; then ok=$((ok+1)); else fail=$((fail+1)); fi; }
[ -x scripts/entropy/verify_entropy.sh ] && { if scripts/entropy/verify_entropy.sh >>"$rep" 2>&1; then ok=$((ok+1)); else fail=$((fail+1)); fi; }
[ -x scripts/sigring/verify_signature_ring.sh ] && { if scripts/sigring/verify_signature_ring.sh >>"$rep" 2>&1; then ok=$((ok+1)); else fail=$((fail+1)); fi; }
[ -x scripts/federate/verify_xref_index.sh ] && { if scripts/federate/verify_xref_index.sh >>"$rep" 2>&1; then ok=$((ok+1)); else fail=$((fail+1)); fi; }
[ -f .tau_ledger/qr/qr-witness.svg ] && echo "qr: present" >>"$rep" || echo "qr: missing" >>"$rep"
[ -f .tau_ledger/interf/interference.svg ] && echo "interference: present" >>"$rep" || echo "interference: missing" >>"$rep"
man="docs/manifest.md"; tmpm="docs/.manifest.gate.$$"; : > "$tmpm"; [ -f "$man" ] || : > "$man"
id="policyv1-$(date -u +%Y%m%dT%H%M%SZ)"; stamp=$(date -u +%Y%m%dT%H%M%SZ)
sha=$(scripts/meta/_sha256.sh "$rep")
status=$([ "$fail" -eq 0 ] && echo "PASS" || echo "FAIL")
while IFS= read -r line; do case "$line" in "## policy_gate (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmpm" ;; esac; done < "$man"
printf "%s\n" "## policy_gate (v1)" >> "$tmpm"; printf "%s\n" "" >> "$tmpm"
printf "%s\n" "id: $id" >> "$tmpm"
printf "%s\n" "utc: $stamp" >> "$tmpm"
printf %'%s\n' "status: $status" >> "$tmpm"
printf "%s\n" "checks_passed: $ok" >> "$tmpm"
printf "%s\n" "checks_failed: $fail" >> "$tmpm"
printf "%s\n" "report: $rep" >> "$tmpm"
printf "%s\n" "report_sha256: $sha" >> "$tmpm"
printf "%s\n" "" >> "$tmpm"; mv "$tmpm" "$man"
echo "policy_gate: $status (passed=$ok failed=$fail) → $rep"
