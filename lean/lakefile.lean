import Lake
open Lake DSL

package «exoverifier» where
  -- Lean 4 uses different dependency management
  -- For now, we'll use the standard library only
  -- If we need mathlib4, we can add it later

@[default_target]
lean_lib «Exoverifier» where
  srcDir := "src"
  -- Root modules will be auto-discovered
