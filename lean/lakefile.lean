import Lake
open Lake DSL

package «exoverifier» where
  -- Add any package configuration settings here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Exoverifier» where
  srcDir := "src"
  -- Root modules will be auto-discovered
