/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Data.Bv.Basic

namespace Bv

theorem eq_succ {n : ℕ} (v₁ v₂ : Fin (n + 1) → Bool) :
    v₁ = v₂ ↔ (v₁ 0 = v₂ 0) ∧ (Fin.tail v₁ = Fin.tail v₂) := by
  constructor
  · intro h; simp [h]
  · intro ⟨h1, h2⟩
    rw [← Fin.cons_self_tail v₁, ← Fin.cons_self_tail v₂, h1, h2]

-- Note: ult (unsigned less than) needs to be defined in Basic first
-- Placeholder for now
-- theorem ult_zero (v₁ v₂ : Fin 0 → Bool) : v₁ < v₂ ↔ False := sorry
-- theorem ult_succ {n : ℕ} (v₁ v₂ : Fin (n + 1) → Bool) : ... := sorry

end Bv
