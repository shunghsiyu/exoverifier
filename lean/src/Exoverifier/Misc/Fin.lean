/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Misc.List

namespace Fin
variable {n : Nat} {α : Type _}

-- Note: Many of the original theorems about list.of_fn are not needed
-- as Lean 4 has Array which is preferred over list-based finite sequences

section reverse

/-- Reverse a tuple (function from Fin n to α). -/
def reverse (v : Fin n → α) : Fin n → α :=
  fun ⟨i, h⟩ => v ⟨n - i - 1, by omega⟩

theorem reverse_last_eq_head (v : Fin (n + 1) → α) :
  reverse v (Fin.last n) = v 0 := by
  simp only [Fin.last, reverse]
  congr 1
  ext
  simp

theorem reverse_reverse (v : Fin n → α) :
  reverse (reverse v) = v := by
  funext ⟨i, hi⟩
  simp only [reverse]
  congr
  omega

end reverse

end Fin
