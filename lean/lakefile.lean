import Lake
open Lake DSL

package exoverifier where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0"

@[default_target]
lean_lib Exoverifier where
  srcDir := "src"
  roots := #[`Misc, `Data, `Sat, `Smt, `Aig, `Btor, `Factory, `Bpf, `Tactic]
