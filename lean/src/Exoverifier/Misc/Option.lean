/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

namespace Option

@[simp]
theorem orelse_eq_none_iff {α : Type _} {x y : Option α} :
  (x <|> y) = none ↔ x = none ∧ y = none :=
  by cases x <;> simp

-- Note: Meta programming (has_to_pexpr) is not needed for core functionality
-- and has changed significantly in Lean 4. Omitting for now.

end Option
