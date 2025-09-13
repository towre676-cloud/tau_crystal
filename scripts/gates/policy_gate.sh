#!/usr/bin/env bash
set -Eeuo pipefail; set +H; umask 022
man="docs/manifest.md"; outdir=".tau_ledger/gates"; stamp=$(LC_ALL=C date -u +%Y%m%dT%H%M%SZ)
id="pgv1-$stamp"; rep="$outdir/$id.txt"; sha="$outdir/$id.sha256"; mkdir -p "$outdir"; : > "$rep"
ok=0; fail=0
runcheck() {
  name="$1"; cmd="$2"; printf "%s\n" "==> $name" >> "$rep"
  if eval "$cmd" >> "$rep" 2>&1; then printf "%s\n" "[OK] $name" >> "$rep"; ok=$((ok+1)); else printf "%s\n" "[FAIL] $name" >> "$rep"; fail=$((fail+1)); fi
}
[ -x scripts/timefold/verify_timefold.sh ] && runcheck "timefold" "scripts/timefold/verify_timefold.sh" || printf "%s\n" "[SKIP] timefold" >> "$rep"
[ -x scripts/signature/verify_signature.sh ] && runcheck "signature" "scripts/signature/verify_signature.sh" || printf "%s\n" "[SKIP] signature" >> "$rep"
[ -x scripts/federate/verify_xref_index.sh ] && runcheck "federation" "scripts/federate/verify_xref_index.sh" || printf "%s\n" "[SKIP] federation" >> "$rep"
[ -x scripts/holo/verify_holo.sh ] && runcheck "holography" "scripts/holo/verify_holo.sh" || printf "%s\n" "[SKIP] holography" >> "$rep"
  else
    printf "%s\n" "[FAIL] sheaf_reflection missing witness $sheaf_id.json" >> "$rep"; fail=$((fail+1))
  fi
else
  printf "%s\n" "[SKIP] sheaf_reflection (no manifest block)" >> "$rep"
fi
printf "%s\n" "" >> "$rep"; printf "checks_passed: %s\n" "$ok" >> "$rep"; printf "checks_failed: %s\n" "$fail" >> "$rep"
scripts/meta/_sha256.sh "$rep" > "$sha"
status="PASS"; [ "$fail" -gt 0 ] && status="FAIL"
tmpm="docs/.manifest.pg.$$"; : > "$tmpm"; [ -f "$man" ] || : > "$man"
while IFS= read -r line; do case "$line" in "## policy_gate (v1)"*) break ;; *) printf "%s\n" "$line" >> "$tmpm" ;; esac; done < "$man"
printf "%s\n" "## policy_gate (v1)" >> "$tmpm"
printf "%s\n" "" >> "$tmpm"
printf "%s\n" "id: $id" >> "$tmpm"
printf "%s\n" "utc: $stamp" >> "$tmpm"
printf "%s\n" "status: $status" >> "$tmpm"
printf "%s\n" "checks_passed: $ok" >> "$tmpm"
printf "%s\n" "checks_failed: $fail" >> "$tmpm"
printf "%s\n" "report: $rep" >> "$tmpm"
printf "%s\n" "report_sha256: $(cat "$sha")" >> "$tmpm"
printf "%s\n" "" >> "$tmpm"
mv "$tmpm" "$man"
echo "policy_gate: $status (passed=$ok failed=$fail) → $rep"
