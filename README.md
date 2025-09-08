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
