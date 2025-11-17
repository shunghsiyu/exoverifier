/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

namespace Option
variable {α : Type*}

@[simp]
theorem orelse_eq_none_iff {x y : Option α} :
    (x <|> y) = none ↔ x = none ∧ y = none := by
  cases x <;> simp

-- Note: Lean 4's metaprogramming system is different from Lean 3
-- The has_to_pexpr functionality would need to be reimplemented using Lean 4's reflection
-- Commenting out for now - can be added later if needed
-- section has_to_pexpr
-- variable [has_to_pexpr α]
-- private meta def to_pexpr' : Option α → pexpr
-- | none     := ``(none)
-- | (some x) := ``(some %%x)
-- meta instance : has_to_pexpr (Option α) := ⟨to_pexpr'⟩
-- end has_to_pexpr

end Option
