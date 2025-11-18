import Lake
open Lake DSL

package «exoverifier» where
  -- Using only Lean 4 standard library for faster compilation

@[default_target]
lean_lib «Exoverifier» where
  srcDir := "src"
  -- Root modules will be auto-discovered
