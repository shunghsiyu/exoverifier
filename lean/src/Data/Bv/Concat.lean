/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Data.Bv.Basic
import Misc.Fin

namespace Bv

-- Note: concat operation needs to be defined in Basic first
-- Placeholder for now

section drop_take
variable {n : ℕ}

/-- Drop the lower i bits. -/
def drop (i : ℕ) (v : Fin n → Bool) : Fin (n - i) → Bool :=
  fun ⟨x, h⟩ => v ⟨x + i, by omega⟩

/-- Extract the lower i bits. -/
def take (i : ℕ) (v : Fin n → Bool) : Fin (min i n) → Bool :=
  fun ⟨x, h⟩ => v ⟨x, Nat.lt_of_lt_of_le h (min_le_right _ _)⟩

-- Theorems about drop/take to be added
-- theorem list_ofFn_drop : ... := sorry
-- theorem list_ofFn_take : ... := sorry

end drop_take

end Bv
