/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.BV.Basic
import Exoverifier.Data.BV.Adc

namespace Fin

/-- Extract all elements except the last one. -/
def init {α : Type _} (v : Fin (n + 1) → α) : Fin n → α :=
  fun i => v i.castSucc

end Fin

namespace BV

variable {n : Nat}

theorem mul_head (v₁ v₂ : Fin (n + 1) → Bool) :
  (v₁ * v₂) 0 = v₁ 0 && v₂ 0 := by
  sorry -- Will complete proof later

theorem mul_tail (v₁ v₂ : Fin (n + 1) → Bool) :
  Fin.tail (v₁ * v₂) = Fin.tail (fun i => v₁ i && v₂ 0) + Fin.init v₁ * Fin.tail v₂ := by
  sorry -- Will complete proof later

end BV
