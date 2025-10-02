import Lake
open Lake DSL

package «HEO» where
  -- you can override more settings here if needed

-- mathlib4 (community library for ℝ, filters, analysis, etc.)
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «HEO»
