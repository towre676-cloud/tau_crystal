# Crash-Proofing Doctrine (CACBE Discipline)

Every shell or script must start with:
`cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1`
`set -euo pipefail; set +H; umask 022`
All file writes use printf (never heredocs). Paths are quoted.
Inputs are validated or defaulted. CI YAML is safely quoted.
Makefiles use real tabs. Windows Git Bash compatibility is assumed.
The linter enumerates violations. The gate blocks until green.

## Canonical Table of Hazards
| Code | Hazard | Signature | Severity |
|---|---|---|---|
| HEREDOC | Heredoc usage in shell | `<<` or `<<-` | High |
| NO_ROOT_CD | Missing repo-root cd guard | script start lacks canonical cd | High |
| NO_STRICT | Missing strict modes | no set -euo pipefail or no set +H | High |
| BAD_VAR | Misspelled or unused var | inconsistent identifier use | High |
| UNQUOTED | Unquoted paths or globs | unquoted $VAR in rm/mv/cp args | High |
| CRLF | DOS line endings | CR bytes in sh or mk | Medium |
| NONASCII | Fancy quotes or symbols | non-ASCII bytes present | Medium |
| YAML_Q | Unsafe Actions quoting | unquoted ${{ }} or colon scalars | Medium |
| MAKE_TAB | Space where tab needed | spaces before make rules | Medium |
| ADB_CONV | MSYS path conversion risk | unquoted remote adb paths | Medium |
| LONG_PASTE | Overlong paste block | single file > 400 lines | Medium |

## Operational Law
Time is central. Quoting is universal. Heredocs are forbidden.
Every change is scanned. The ledger ranks hazards by count x severity.
Blocking on red turns debugging into prevention. Ledger: `.tau_ledger/cacbe/`.
