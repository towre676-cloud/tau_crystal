#!/usr/bin/env bash
set -euo pipefail

REPO="$HOME/Desktop/tau_crystal/tau_crystal"
cd "$REPO" || { echo "[err] repo root not found: $REPO"; exit 1; }

export GIT_TERMINAL_PROMPT=0
branch="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo main)"

dirty="$(git status --porcelain)"
STASH_REF=""
# PULL modes:
#   PULL=0 (default): skip pull if dirty
#   PULL=1: if dirty, auto-stash untracked+tracked; pull; keep stash (don't auto-pop)
PULL="${PULL:-0}"

# 1) fetch + optional fast-forward pull
if git rev-parse --abbrev-ref @{u} >/dev/null 2>&1; then
  git fetch --quiet || true
  if [ -n "$(git rev-list HEAD..@{u} 2>/dev/null)" ]; then
    if [ -n "$dirty" ] && [ "$PULL" = "0" ]; then
      echo "[pull] skipped fast-forward: working tree dirty. (set PULL=1 to auto-stash)"
    else
      if [ -n "$dirty" ]; then
        STASH_REF="$(git stash push -u -m "audit_autostash_$(date -u +%Y%m%dT%H%M%SZ)" | sed -n '1p')"
        echo "[pull] auto-stashed: ${STASH_REF}"
      fi
      git pull --rebase --quiet || echo "[pull] non-fatal: rebase not applied"
    fi
  fi
fi

issues=()

# 2) spec vs manifest version (jq path used when available)
spec="docs/specs/manifest-v1.1.md"
man="tau-crystal-manifest.json"
rcpt="tau-crystal-receipt.json"

spec_ver="missing"
[ -f "$spec" ] && spec_ver="$(awk '/^[# ]*[Vv]ersion/{print $NF; exit}' "$spec" || echo missing)"

man_ver="missing"
if [ -f "$man" ]; then
  if command -v jq >/dev/null 2>&1; then
    man_ver="$(jq -r '.version // "missing"' "$man")"
  else
    man_ver="$(grep -oE '"version"[[:space:]]*:[[:space:]]*"[^"]+"' "$man" | sed -E 's/.*"version"[[:space:]]*:[[:space:]]*"([^"]*)".*/\1/' | head -n1 || echo missing)"
  fi
fi
[ "$spec_ver" != "$man_ver" ] && issues+=("Spec declares $spec_ver but manifest uses $man_ver")

# 3) receipt must mirror manifest.merkle_root
if [ -f "$man" ] && [ -f "$rcpt" ]; then
  if command -v jq >/dev/null 2>&1; then
    if ! jq -e '.merkle_root as $m | .reflective.merkle_root == $m' "$rcpt" >/dev/null; then
      issues+=("Receipt reflective.merkle_root != manifest.merkle_root")
    fi
  else
    mroot="$(grep -oE '"merkle_root"[[:space:]]*:[[:space:]]*"[^"]*"' "$man"  | sed -E 's/.*"merkle_root"[[:space:]]*:[[:space:]]*"([^"]*)".*/\1/' | head -n1)"
    rrefl="$(grep -oE '"reflective"[[:space:]]*:[[:space:]]*\{[^}]*\}' "$rcpt" | grep -oE '"merkle_root"[[:space:]]*:[[:space:]]*"[^"]*"' | sed -E 's/.*"merkle_root"[[:space:]]*:[[:space:]]*"([^"]*)".*/\1/' | head -n1)"
    [ -n "$mroot" ] && [ -n "$rrefl" ] && [ "$mroot" != "$rrefl" ] && issues+=("Receipt reflective.merkle_root != manifest.merkle_root")
  fi
fi

# 4) CRLF contamination (text files only)
if git ls-files -z | xargs -0 -I{} sh -c "grep -Iq . '{}' && grep -q $'\r' '{}'" >/dev/null 2>&1; then
  issues+=("Text files contain CRLF line endings")
fi

# 5) oversized tracked files not archives
biglist="$(git ls-files -z | xargs -0 ls -l 2>/dev/null | awk '$5>1048576{print $9}')"
if [ -n "$biglist" ]; then
  while IFS= read -r p; do
    case "$p" in
      *.zip|*.tar.gz|*.tgz|*.gz|*.7z|*.rar|*.ots|*.png|*.jpg|*.jpeg) : ;;
      *) issues+=("Large tracked file (>1MiB): $p (consider LFS)") ;;
    esac
  done <<< "$biglist"
fi

# 6) SPDX headers in Python scripts
for f in scripts/*.py; do
  [ -f "$f" ] || continue
  if ! head -1 "$f" | grep -qE '^# SPDX-License-Identifier:'; then
    issues+=("Missing SPDX header in $f")
  fi
done

# 7) CI matrix fail-fast suggestion
if ls .github/workflows/*.y*ml >/dev/null 2>&1; then
  if grep -q 'strategy:.*matrix' .github/workflows/*.y*ml && ! grep -q 'fail-fast:[[:space:]]*false' .github/workflows/*.y*ml; then
    issues+=("CI matrix: recommend 'fail-fast: false'")
  fi
fi

# 8) loose objects check
loose="$(git count-objects -v 2>/dev/null | awk '/count:/ {print $2}')"
[ "${loose:-0}" -gt 500 ] && issues+=("Loose objects >500; run 'git gc --aggressive' before release")

# 9) launcher strict opts
launcher="scripts/plan/launch_verifiers.sh"
if [ -f "$launcher" ] && ! grep -q 'set -euo pipefail' "$launcher"; then
  issues+=("Launcher lacks 'set -euo pipefail'")
fi

# Report
if [ "${#issues[@]}" -eq 0 ]; then
  echo "[✓] No issues detected; repo looks reference‑grade."
else
  echo "[!] Found ${#issues[@]} polish items:"
  printf '  - %s\n' "${issues[@]}"
fi

# Auto-fix when APPLY=1
if [ "${APPLY:-0}" = "1" ]; then
  echo "[fix] applying safe fixes…"
  changed=0

  # CRLF → LF (text files only)
  if printf '%s\n' "${issues[@]}" | grep -q 'CRLF'; then
    while IFS= read -r f; do
      grep -Iq . "$f" || continue
      if grep -q $'\r' "$f"; then
        tmp="$(mktemp)"; tr -d '\r' <"$f" >"$tmp" && mv "$tmp" "$f"; changed=1
      fi
    done < <(git ls-files)
  fi

  # SPDX headers
  for f in scripts/*.py; do
    [ -f "$f" ] || continue
    if ! head -1 "$f" | grep -qE '^# SPDX-License-Identifier:'; then
      tmp="$(mktemp)"; { echo "# SPDX-License-Identifier: MIT"; cat "$f"; } >"$tmp" && mv "$tmp" "$f"; changed=1
    fi
  done

  # launcher strict opts
  if [ -f "$launcher" ] && ! grep -q 'set -euo pipefail' "$launcher"; then
    tmp="$(mktemp)"; awk 'NR==1{print; print "set -euo pipefail"; next}1' "$launcher" >"$tmp" && mv "$tmp" "$launcher"; changed=1
  fi

  # git gc if needed
  [ "${loose:-0}" -gt 500 ] && git gc --aggressive --quiet || true

  if [ "$changed" -eq 1 ]; then
    git add -A
    git commit -m "audit: polish fixes (CRLF/SPDX/strictOpts)" || true
  fi
fi

# Scorecard (with jq if present)
mkdir -p docs
{
  echo "# τ-Crystal Ledger Scorecard — Reference Grade Audit"
  echo
  echo "- **Spec/Manifest Version Sync**: $([ "$spec_ver" = "$man_ver" ] && echo PASS || echo FAIL)"
  if [ -f "$man" ] && [ -f "$rcpt" ]; then
    if command -v jq >/dev/null 2>&1; then
      ok="$(jq -e '(.reflective.merkle_root // null) as $r | .merkle_root == $r' "$rcpt" >/dev/null && echo PASS || echo FAIL)"
      echo "- **Receipt ↔ Manifest Root**: $ok"
    else
      echo "- **Receipt ↔ Manifest Root**: CHECKED (no jq)"
    fi
  else
    echo "- **Receipt ↔ Manifest Root**: SKIP"
  fi
  if git ls-files -z | xargs -0 -I{} sh -c "grep -Iq . '{}' && grep -q $'\r' '{}'" >/dev/null 2>&1; then
    echo "- **CRLF Contamination**: FAIL"
  else
    echo "- **CRLF Contamination**: PASS"
  fi
  bign="$(printf '%s\n' "$biglist" | wc -l | tr -d ' ')"; [ -z "$biglist" ] && bign=0
  echo "- **Large Text in LFS**: $([ "$bign" -eq 0 ] && echo PASS || echo FAIL)"
  echo "- **Loose Objects ≤500**: $([ "${loose:-0}" -le 500 ] && echo PASS || echo FAIL)"
  spdx_ok=PASS
  for f in scripts/*.py; do [ -f "$f" ] || continue; head -1 "$f" | grep -qE '^# SPDX-License-Identifier:' || spdx_ok=FAIL; done
  echo "- **SPDX Headers**: $spdx_ok"
  echo
  echo "Generated on: $(date -u +"%Y-%m-%dT%H:%M:%SZ")"
} > docs/LEDGER_SCORECARD.md
git add docs/LEDGER_SCORECARD.md
git commit -m "audit: reference-grade scorecard" || true

# Optional push (only when PUSH=1)
if [ "${PUSH:-0}" = "1" ]; then
  git push origin "$branch" || true
fi

# If we auto-stashed for pull, leave it for you to inspect/pop
[ -n "${STASH_REF}" ] && echo "[pull] note: changes stashed (${STASH_REF}). Use 'git stash list' / 'git stash show -p' / 'git stash pop'."

echo "[done] audit complete on branch '$branch'."
