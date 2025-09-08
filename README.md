Drop this action in place of leanprover/lean-action; get 3× better Mathlib caching; verify in 10s.

## Lean SmartCache Quick Start

```yaml
- uses: actions/checkout@v4
- uses: ./.github/actions/lean-smart
  with:
    working-directory: .
    elan-toolchain: "leanprover/lean4:v4.22.0"
```

# Lean CI (SmartCache)

**What it is**  
A composite GitHub Action that runs Lean 4 builds and **caches artifacts keyed to your `mathlib` revision**.
After the first run, PR builds typically reuse the cache when `mathlib` hasn’t changed.

**Why not just `leanprover/lean-action`?**  
This adds a *smart* cache key: `OS + elan toolchain + lakefile hash + mathlib rev`.
That makes cache hits more consistent across PRs that don’t bump mathlib.

**Usage**
```yaml
- uses: actions/checkout@v4
- uses: ./.github/actions/lean-smart
  with:
    working-directory: .
    smart-cache: "true"
```

## Lean SmartCache Quick Start
Drop this action in place of the official one. It hydrates Mathlib by exact commit from GHCR and falls back to a normal build on a miss.

```yaml
- uses: actions/checkout@v4
- uses: ./.github/actions/lean-smart
  with:
    working-directory: .
    elan-toolchain: "leanprover/lean4:v4.22.0"
```

Verify any emitted receipt in one step:

```bash
lake manifest verify
```

<!-- cache-hit demo 20250908-180558 -->
