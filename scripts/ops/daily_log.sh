#!/usr/bin/env bash
# Hardened daily logger: Windows-safe, no network, section-isolated, supports SNAPSHOT_DATE=YYYYMMDD (UTC)
set -u; set +e; set +o pipefail; umask 022; export LC_ALL=C LANG=C

section(){ printf "%s\n" "$1" >> "$TMP"; }
iso_from_yyyymmdd(){ local d="$1"; printf "%s-%s-%s" "${d:0:4}" "${d:4:2}" "${d:6:2}"; }

TODAY_UTC="${SNAPSHOT_DATE:-$(date -u +%Y%m%d)}"
NOW_UTC="$(date -u +%Y%m%dT%H%M%SZ)"
ISO_DAY="$(iso_from_yyyymmdd "$TODAY_UTC")"
MIDNIGHT_UTC="${ISO_DAY}T00:00:00Z"

LOG=".tau_ledger/daily/${TODAY_UTC}.log"
TMP=".cache/daily_${TODAY_UTC}_$$.tmp"
mkdir -p .tau_ledger/daily .cache
: > "$TMP"

{
  echo "==== TAU-CRYSTAL DAILY LOG ===="
  echo "date_utc: $NOW_UTC"
  echo "day_utc:  $TODAY_UTC"
  echo "repo: $(pwd)"
  echo
} >> "$TMP"

export GIT_PAGER=cat GIT_OPTIONAL_LOCKS=0

section "== git/identity (hardened) =="
{
  if timeout 3s git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    BRANCH="$(timeout 2s git rev-parse --abbrev-ref HEAD 2>/dev/null || echo '(none)')"
    HEADREF="$(timeout 2s git rev-parse HEAD 2>/dev/null || echo '(none)')"
    echo "branch: $BRANCH"
    echo "head:   $HEADREF"
    echo "remote(s):"
    if timeout 2s git remote -v 2>/dev/null >/tmp/.rem_$$; then
      sed 's/^/  /' </tmp/.rem_$$
      rm -f /tmp/.rem_$$
    else
      echo "  (unable to read remotes quickly)"
    fi
  else
    echo "(not a git repository here)"
  fi
  echo
} >> "$TMP" 2>/dev/null

section "== git/status (hardened) =="
{
  if timeout 3s git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    timeout 5s git -c status.submoduleSummary=false status --porcelain=v1 -z -uno 2>/dev/null | tr '\0' '\n' \
      || { echo "(git status timed out; fallback ls-files)"; timeout 5s git ls-files -m -o --exclude-standard 2>/dev/null | sed 's/^/  /'; }
  else
    echo "(not a git repository here)"
  fi
  echo
} >> "$TMP" 2>/dev/null

section "== git/diff --cached (summary) =="
git diff --cached --stat 2>/dev/null >> "$TMP"; echo >> "$TMP"

section "== git/diff --cached (patch) =="
git diff --cached 2>/dev/null >> "$TMP"; echo >> "$TMP"

section "== git/diff (summary) =="
git diff --stat 2>/dev/null >> "$TMP"; echo >> "$TMP"

section "== git/diff (patch) =="
git diff 2>/dev/null >> "$TMP"; echo >> "$TMP"

section "== git/log since 00:00Z =="
git log --since="${ISO_DAY} 00:00" --pretty=format:"%H %ad %an %s" --date=iso-strict 2>/dev/null >> "$TMP"; echo >> "$TMP"

section "== git/log --name-status since 00:00Z =="
git log --since="${ISO_DAY} 00:00" --name-status --pretty="tformat:" 2>/dev/null >> "$TMP"; echo >> "$TMP"

section "== fs/mtime touched today (UTC) =="
if timeout 3s bash -lc 'find . -type f -not -path "./.git/*" -newermt "'"${ISO_DAY} 00:00"'" -printf "%TY-%Tm-%TdT%TH:%TM:%TSZ %p\n" >/dev/null 2>&1'; then
  bash -lc 'find . -type f -not -path "./.git/*" -newermt "'"${ISO_DAY} 00:00"'" -printf "%TY-%Tm-%TdT%TH:%TM:%TSZ %p\n"' 2>/dev/null | sort >> "$TMP"
else
  if command -v powershell.exe >/dev/null 2>&1; then
    powershell.exe -NoLogo -NoProfile -Command "
      \$mid=[DateTime]::Parse('$MIDNIGHT_UTC',[Globalization.CultureInfo]::InvariantCulture,[System.Globalization.DateTimeStyles]::AdjustToUniversal);
      Get-ChildItem -Recurse -File -Force |
        Where-Object { \$_.FullName -notmatch '\.git(\|/)' -and \$_.LastWriteTimeUtc -ge \$mid } |
        ForEach-Object { '{0:yyyy-MM-ddTHH:mm:ssZ} {1}' -f \$_.LastWriteTimeUtc, (Resolve-Path -LiteralPath \$_.FullName).Path } |
        Sort-Object
    " 2>/dev/null | sed 's#\r$##' >> "$TMP"
  else
    echo "(fallback) powershell.exe not found; showing tracked files changed in git since midnight" >> "$TMP"
    git log --since="${ISO_DAY} 00:00" --name-only --pretty=tformat: 2>/dev/null | sed '/^$/d' | sort -u | sed 's/^/  /' >> "$TMP"
  fi
fi
echo >> "$TMP"

section "== fs/top changed sizes today =="
if command -v powershell.exe >/dev/null 2>&1; then
  powershell.exe -NoLogo -NoProfile -Command "
    \$mid=[DateTime]::Parse('$MIDNIGHT_UTC',[Globalization.CultureInfo]::InvariantCulture,[System.Globalization.DateTimeStyles]::AdjustToUniversal);
    Get-ChildItem -Recurse -File -Force |
      Where-Object { \$_.FullName -notmatch '\.git(\|/)' -and \$_.LastWriteTimeUtc -ge \$mid } |
      Select-Object Length, FullName |
      Sort-Object Length -Descending |
      Select-Object -First 25 |
      ForEach-Object { '{0} {1}' -f \$_.Length, (Resolve-Path -LiteralPath \$_.FullName).Path }
  " 2>/dev/null | sed 's#\r$##' >> "$TMP"
else
  echo "(fallback) powershell.exe not found; skipping FS sizes" >> "$TMP"
fi
echo >> "$TMP"

section "== git/untracked =="
git ls-files --others --exclude-standard 2>/dev/null | sed 's/^/  /' >> "$TMP"; echo >> "$TMP"

section "== actions/workflows present =="
find .github/workflows -maxdepth 1 -type f 2>/dev/null | sed 's/^/  /' >> "$TMP" || echo "  (none)" >> "$TMP"; echo >> "$TMP"

section "== digest =="
SHA=""
if command -v sha256sum >/dev/null 2>&1; then
  SHA="$(sha256sum "$TMP" | awk '{print $1}')"
elif command -v openssl >/dev/null 2>&1; then
  SHA="$(openssl dgst -sha256 "$TMP" | awk '{print $2}')"
elif command -v certutil >/dev/null 2>&1; then
  # certutil prints a header+footer; second line is the hash
  SHA="$(certutil -hashfile "$(cygpath -w "$TMP")" SHA256 2>nul | awk 'NR==2{print $1}')"
else
  SHA="UNAVAILABLE"
fi
echo "sha256: $SHA" >> "$TMP"

mv -f "$TMP" "$LOG"
echo "[daily] wrote $LOG"
echo "[daily] sha256=$SHA"
