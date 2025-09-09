<!-- BEGIN: front-promise -->
> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (<=10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```
<!-- END: front-promise -->
<!-- BEGIN: reproducibility-identity -->
## Reproducibility: no heuristics, just identity

**We bind each run to a runner fingerprint (kernel + image label + glibc) *and* the SHA-256 of every binary that executes; any drift flips the chain head.**  

That’s strictly stronger than any “what files were touched” heuristic. We don’t infer reproducibility from filesystem behavior—we prove it from identities.

### Why filesystem checks don’t matter here
- `df` answers “did we nearly run out of space?”; our receipt makes that irrelevant. Either the build completes and emits the **same chain head** or it fails fast. There’s no “passed but different” in between.
- Filesystem usage heuristics watch *effects* (I/O, free space). We certify *causes*: **the exact machine and the exact executables** involved.

### What flips the chain head (by design)
- Kernel or runner image changes (captured in the **runner fingerprint**).
- C library / loader changes (glibc version in the fingerprint).
- **Any** executable’s bytes that participate (compiler, linker, lake/lean, scripts we hash) change.
- Pinned workflow/action SHAs or toolchain pins change.

### What does **not** flip it (and shouldn’t)
- Disk free space, inode ordering, or layout changes that don’t alter the runner or executables.
- Cosmetic log differences, path noise, or unrelated files outside the attested graph.

### Practical footnotes (for honesty)
Reproducibility doesn’t excuse unpinned inputs or non-deterministic sources. We already pin the platform and executables; you should also **fix/record** when relevant:
- `TZ`, `LANG` / `LC_*` (locale), RNG seeds
- Network access (ideally off), environment variables that affect numerics
- (Optional/harder) CPU microcode/flags—our schema has room to extend the fingerprint

> **Core guarantee:** if the kernel/image/glibc or any participating binary changes, the receipt changes.  
> If none of them change, the chain head stays identical—regardless of disk usage or filesystem quirks.
<!-- END: reproducibility-identity -->
<!-- BEGIN: status-badges -->
<div align="left">

[![assure](https://github.com/towre676-cloud/tau_crystal/actions/workflows/assure.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/assure.yml) 
[![cross-OS nightly](https://github.com/towre676-cloud/tau_crystal/actions/workflows/cross-os-nightly.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/cross-os-nightly.yml) 
[![CodeQL](https://github.com/towre676-cloud/tau_crystal/actions/workflows/codeql.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/codeql.yml)

[Release v1.1.0](https://github.com/towre676-cloud/tau_crystal/releases/tag/v1.1.0) · [Workflows](https://github.com/towre676-cloud/tau_crystal/actions)

</div>
<!-- END: status-badges -->
# τ-Crystal — **3× faster Mathlib caching** for Lean CI (Linux, containerized)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

<!-- BEGIN: three-streams -->

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Three Streams, One Deterministic Proof Path

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

τ-Crystal produces a canonical receipt, commits an append-only transparency leaf, and writes the current Merkle head back into the receipt in one step. Clone, build, and verify without extra tooling or guesswork.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

| Stream | What it emits | Invariant guaranteed | Where it lives | How it’s sealed |

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

|---|---|---|---|---|

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

| Grammar | Canonical grammar and digest inputs to the receipt | Same source, same digest; CRLF-safe, locale-safe | `.tau_ledger/receipt.json` | Receipt carries `grammar_digest` and `grammar_algo` |

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

| Statement | Canonical statement and digest, plus run metadata | Deterministic content and ordering; reproducible from a clean clone | `.tau_ledger/receipt.json` | Receipt carries `statement_digest` and `statement_algo` |

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

| Transparency | Append-only Merkle leaf and rolling tree head | Every build appends once; tree head is reproducible from frontier | `.tau_ledger/tlog.ndjson`, `.tau_ledger/merkle_state.txt` | `tlog_append.sh` embeds `tlog_leaf`, `tlog_root`, `tlog_index`, `tlog_algo` |

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# one-shot local transparency (writes tlog_* back into receipt):

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

RECEIPT_PATH=.tau_ledger/receipt.json scripts/tlog_append.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

<!-- END: three-streams -->

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

![CI: lean-minicache](https://github.com/towre676-cloud/tau_crystal/actions/workflows/lean-minicache.yml/badge.svg?branch=main)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

Drop this repo's **`.github/workflows/lean-minicache.yml`** into your project (or copy the fragment). It caches **Mathlib** by exact commit and runs inside a prebuilt Lean container, so PRs on the same Mathlib SHA usually build **3–6× faster**—no registries, no ORAS.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

### Quick Start

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Use **Linux runners** only (faster on GitHub-hosted).

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Keep PRs on the **same Mathlib commit** to preserve cache hits.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Copy or adapt: `.github/workflows/lean-minicache.yml`.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- After two runs (fresh + hydrated), record times in **[docs/BENCHMARK.md](docs/BENCHMARK.md)**.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

### What you get

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- **Mathlib-only cache** keyed by exact SHA → biggest time win with minimal risk.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- **Prebuilt Lean container** → skips toolchain install (~20–40s saved).

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- **Step Summary** prints build time and cache key on every run.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![Plan: FREE](https://img.shields.io/badge/plan-FREE-blue?style=flat-square)](./.tau_plan_roots.env)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![CI](https://img.shields.io/github/actions/workflow/status/towre676-cloud/tau_crystal.git/verify.yml?style=flat-square)](https://github.com/towre676-cloud/tau_crystal.git/actions)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![Attestation](https://img.shields.io/badge/attestation-ledger-green?style=flat-square)](./.tau_ledger/attestation.txt)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# τ-Crystal

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Plans

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

**τ‑Crystal** is free for public repos and small private experiments.  

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

**Pro** ($12k/year) turns it into an org-grade verification spine:

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Organization-wide SSO and policy enforcement

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- 10× CI throughput with formal proof gates required

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- 180-day manifest retention, Merkle root stamping

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Receipt chain with immutable attestation export

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

If your auditors, insurers, or treasury depend on this, you want **Pro**.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![Live τ](https://img.shields.io/badge/gh--pages-live%20τ-blue)](https://towre676-cloud.github.io/tau_crystal/sample/live.html)  

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[Monograph](https://towre676-cloud.github.io/tau_crystal/MONOGRAPH/) · 

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[Repository](https://github.com/towre676-cloud/tau_crystal)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

The project certifies not merely outputs but execution paths. Every build binds a geometric tau-clock to a Lean 4 program and emits a compact, cryptographically stable manifest that can be replayed, diffed, and audited without ambiguity. The result is a proof-carrying runtime receipt for scientific compute: identical inputs, identical path, identical proof. If two runs diverge, the manifest makes the point of divergence explicit and machine-checkable, collapsing weeks of forensics into a deterministic, one-line comparison. The repository is intentionally small and strict. Lake orchestrates the Lean toolchain; the executable graph emits a canonical receipt; the CI harness fixes the invariant grammar so that a receipt from today can be inspected tomorrow and still verify byte-for-byte.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

![CI: assure.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/assure.yml/badge.svg?branch=main)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

![CI: ci.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/ci.yml/badge.svg?branch=main)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

![CI: codeql.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/codeql.yml/badge.svg?branch=main)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

![CI: ledger-tau.yml](https://github.com/towre676-cloud/tau_crystal/actions/workflows/ledger-tau.yml/badge.svg?branch=main)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

Getting started is a two-command path on any machine with a recent toolchain. First, install elan (which supplies Lean and Lake) and confirm the versions; second, build the library and invoke a single assurance script that emits a canonical manifest. The same commands run in CI and on your desktop so the attestation story is uniform.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# one-time toolchain (Git Bash)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

export PATH="$HOME/.elan/bin:$PATH"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

lean --version

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

lake --version

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# repo root: build and assure

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

lake build

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

./scripts/assure.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

---

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

Read the monograph: [docs/MONOGRAPH.md](docs/MONOGRAPH.md)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

---

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![Receipt Verified](https://img.shields.io/badge/tau--crystal-receipt--verified-brightgreen?logo=github)](docs/manifest.md)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![τ‑Crystal Verified](https://img.shields.io/badge/receipt-verified-brightgreen?logo=github)](docs/manifest.md)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[![receipt-verified](https://img.shields.io/badge/receipt-verified-brightgreen)](https://towre676-cloud.github.io/tau_crystal/tau-crystal.html)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

—

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

See **[CI Pipeline](docs/CI.md)** · **[License](LICENSE)** · **[Sample HTML](docs/sample/live.html)**

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Quickstart

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## τ-Crystal — proof-carrying runtime manifest for reproducible compute

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

τ-Crystal turns a repository into a self-verifying project. Every run emits a receipt chained by SHA-256, stamps a repository-wide MERKLE_ROOT over tracked files, and writes a live STATUS line to docs/manifest.md. The result is a one-line, machine-checkable claim you can quote in issues, papers, and audits.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

**Why it matters:** traditional pipelines hash outputs or bundle environments, but they don’t prove the execution path. τ-Crystal makes divergence explicit and small: the CHAIN head changes if and only if the verified path changed.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

**What you get today (bash-only):**

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

– Execution-state receipts + CHAIN

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

– Repository MERKLE_ROOT + manifest STATUS

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

– Same flow locally and in CI (no containers required)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

– Free tier to prove value; Pro adds required proof gates, higher throughput, and longer retention

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

**Prove it fast:** run the pinned “Verify this release (v0.1.1)” snippet below, then try the Golden diff demo (perturb one tracked file and watch the head change). Keep your science/dev runnable—and provable—without heavy tooling. When you need org-wide enforcement, turn on Pro.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Verify this release (v0.1.1)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# fetch and checkout the release tag

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

git fetch --tags --quiet && git checkout v0.1.1

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# run the built-in chain + manifest checks

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/plan/tau_pro_gate.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/plan/write_roots.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-4} ./scripts/plan/launch_verifiers.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# 1) CHAIN head must match the sha256 of its receipt file

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

rcpt=$(awk '{p=$2; h=$1} END{print p}' .tau_ledger/CHAIN)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

head=$(awk 'END{print $1}' .tau_ledger/CHAIN)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

calc=$(sha256sum "$rcpt" | awk '{print $1}')

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[ "$calc" = "$head" ] && echo "OK: chain head verified" || echo "FAIL: chain head mismatch"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# 2) Manifest merkle_root must equal receipt.reflective.merkle_root

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

if command -v jq >/dev/null 2>&1; then

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

  m="$(jq -r .merkle_root tau-crystal-manifest.json 2>/dev/null)"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

  r="$(jq -r .reflective.merkle_root "$rcpt" 2>/dev/null)"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

else

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

  m="$(grep -oE "\"merkle_root\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" tau-crystal-manifest.json | sed -E "s/.*:\"([^\"]*)\".*/\1/" | head -n1)"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

  r="$(grep -oE "\"merkle_root\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" "$rcpt" | head -n1 | sed -E "s/.*:\"([^\"]*)\".*/\1/")"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

fi

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[ -n "$m" ] && [ "$m" = "$r" ] && echo "OK: manifest ↔ receipt root" || echo "FAIL: root mismatch"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# from repo root

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/plan/tau_pro_gate.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/plan/write_roots.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-20} ./scripts/plan/launch_verifiers.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Latest status: see `docs/manifest.md` (STATUS + MERKLE_ROOT)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Receipts: `.tau_ledger/receipts/`

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Chain head: `.tau_ledger/CHAIN`

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Human summary: `.tau_ledger/attestation.txt`

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Docs

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- **Manifest spec**: `docs/specs/manifest-v1.1.md` (if present)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- **Live manifest**: `docs/manifest.md`

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- **Ledger attestation**: `.tau_ledger/attestation.txt`

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- **Audit guide**: `docs/AUDIT.md`

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- **CI notes**: `docs/ci.md`

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Why this is different

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

Traditional pipelines hash results; **τ‑Crystal hashes the *execution state***.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

Each run emits a SHA‑256 chained receipt, stamps a Merkle root over tracked files,

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

and writes a STATUS line to the manifest. Divergence is not hidden; it’s **explicit,

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

small, and machine‑checkable** — so you can quote a single line to prove what ran.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Golden diff (10 lines)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# 1) baseline receipt

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/plan/write_roots.sh; TAU_MAX_SHARDS=2 ./scripts/plan/launch_verifiers.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

base="$(tail -n1 .tau_ledger/CHAIN | awk '{print $1}')" 

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# 2) tiny perturbation to a tracked file (no commit); rerun

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

printf " " >> README.md

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/plan/write_roots.sh; TAU_MAX_SHARDS=2 ./scripts/plan/launch_verifiers.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

head="$(tail -n1 .tau_ledger/CHAIN | awk '{print $1}')" 

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# 3) print the one‑line diff and revert the perturbation

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[ "$base" = "$head" ] && echo "expected a diff, got none" || echo "golden diff: $base -> $head"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

git checkout -- README.md

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Verify this repo (current commit)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Why tanh?

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- One-soliton: u = 2 ∂_x^2 log(1 + e^θ) collapses to (k^2/2) sech^2(θ/2), with θ = k x + δ at t = 0.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- τ-function (2-soliton): u = 2 ∂_x^2 log τ where τ = det(I + M); after identities the field organizes as sums/products of tanh^2.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Gudermannian: φ = gd(κ x) maps ℝ to S^1 to place modulation checks on a compact angle.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

- Determinism: we hash fixed-point envelopes for cross-OS stability and put hashes in the ledger/manifest.

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Verify soliton demos

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# one-soliton envelope: JSON + hash into .tau_ledger/soliton_envelope.json

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/run_soliton_envelope.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

cat .tau_ledger/soliton_envelope.json | (jq -r ".sha256" 2>/dev/null || grep -oE "\"sha256\":\"[0-9a-fA-F]+\"" | sed -E "s/.*:\"([0-9a-fA-F]+)\".*/\1/")

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# two-soliton τ/tanh demo: JSON + image (PNG if ImageMagick, else PGM)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/run_tau_tanh_demo.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

cat .tau_ledger/tau_tanh_2soliton.json | (jq -r ".sha256" 2>/dev/null || grep -oE "\"sha256\":\"[0-9a-fA-F]+\"" | sed -E "s/.*:\"([0-9a-fA-F]+)\".*/\1/")

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

ls -l media/tau_tanh_demo.png 2>/dev/null || echo "open media/tau_tanh_demo.pgm"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# stamp both hashes into docs/manifest.md (idempotent)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/stamp_soliton_into_manifest.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/stamp_tau_tanh_into_manifest.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

Tested at: https://github.com/towre676-cloud/tau_crystal/tree/f9d86ab4714884ff3874de4e5f089f4c40ac25e4

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

bash scripts/verify_release_state.sh

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Verify this release (cosign)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```bash

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# set these for your asset(s)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

TAG=v0.1.0

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

FILE=tau_crystal-$TAG.tgz

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

DIGEST=sha256:<image-or-asset-digest>

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# verify signed SBOM attestation (CycloneDX) for container/image (if published)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

cosign verify-attestation --type cyclonedx \n  --certificate-oidc-issuer 'https://token.actions.githubusercontent.com' \n  --certificate-identity 'https://github.com/towre676-cloud/tau_crystal/.github/workflows/release.yml@refs/tags/' \n  ghcr.io/towre676-cloud/tau_crystal@"$DIGEST"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

# verify tarball against its .sig + .cert (blob)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

cosign verify-blob --certificate "$FILE.cert" --signature "$FILE.sig" "$FILE"

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

## Expected success

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[OK] chain head = <sha> (receipt = .tau_ledger/receipts/...json)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

[OK] merkle_root = <sha> (manifest ↔ receipt)

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

```

> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```



> **Every run emits a SHA-256 receipt that proves the exact execution path; change one byte and the chain head flips.**

### Quick verify (≤10s, Bash)
```bash
# from repo root
bash scripts/plan/write_roots.sh >/dev/null 2>&1
TAU_MAX_SHARDS=${TAU_MAX_SHARDS:-2} ./scripts/plan/launch_verifiers.sh >/dev/null 2>&1
rcpt=$(awk "{p=\$2} END{print p}" .tau_ledger/CHAIN); head=$(awk "END{print \$1}" .tau_ledger/CHAIN)
echo "CHAIN_HEAD=$head"
[ -f "$rcpt" ] && echo "RECEIPT=$rcpt"
```

### Windows (PowerShell)
```powershell
# one-time toolchain
iwr -useb https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | iex
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
lake build
./scripts/assure.sh
```

