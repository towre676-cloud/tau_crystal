# Crash‑Proofing Doctrine (CACBE‑Proof Discipline)

Every shell/script fragment must begin by asserting the working root, enforcing strict error handling, disabling history expansion, and defaulting to portable POSIX behavior: `cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1; set -euo pipefail; set +H; umask 022`. All file writes are performed with printf (never heredocs), all paths are quoted, and all environment inputs are validated or defaulted. CI YAML is strictly quoted; Makefiles use real tabs; Windows Git Bash compatibility is assumed. The linter enumerates violations and the gate refuses commits until the attention ledger is green.

## Canonical Table of Hazards
| Code | Hazard | Signature | Severity |
|---|---|---|---|
| HEREDOC | Heredoc usage in shell | `<<` or `<<-` | High |
| NO_ROOT_CD | Missing repo‑root `cd` guard | start of script lacks canonical cd | High |
| NO_STRICT | Missing `set -euo pipefail` or `set +H` | absent or overridden | High |
| BAD_VAR | Misspelled/unused var names | inconsistent identifier use | High |
| UNQUOTED | Unquoted paths/globs | unquoted $VAR in rm/mv/cp args | High |
| CRLF | DOS line endings in sh/mk | CR bytes present | Medium |
| NONASCII | Fancy quotes / non‑ASCII | U+2018/2019/201C/201D present | Medium |
| YAML_Q | Unsafe GitHub Actions quoting | unquoted ${{ }} or YAML scalars with colons | Medium |
| MAKE_TAB | Space where tab required | spaces before make rules | Medium |
| ADB_CONV | MSYS path conversion risk | unquoted remote adb paths | Medium |
| LONG_PASTE | Overlong paste blocks | single pasted file > 400 lines | Medium |

## Operational Law
Time is central, quoting is universal, heredocs are forbidden, and every change is scanned. The ledger ranks hazards by frequency×severity (attention score) and blocks on red. “Debugging” becomes structural prevention recorded in `.tau_ledger/cacbe/`.
