/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.BV.Basic
import Exoverifier.Data.BV.Adc

namespace Fin

/-- Prepend an element to a function from Fin n to α. -/
def cons {α : Type _} (x : α) (v : Fin n → α) : Fin (n + 1) → α :=
  fun i => if h : i.val = 0 then x else v ⟨i.val - 1, by omega⟩

theorem cons_zero {α : Type _} (x : α) (v : Fin n → α) :
  cons x v 0 = x := by
  unfold cons
  simp

theorem cons_succ {α : Type _} (x : α) (v : Fin n → α) (i : Fin n) :
  cons x v i.succ = v i := by
  unfold cons
  simp

theorem cons_self_tail {α : Type _} (v : Fin (n + 1) → α) :
  cons (v 0) (tail v) = v := by
  sorry -- Will complete proof later

end Fin

namespace BV

theorem eq_succ {n : Nat} (v₁ v₂ : Fin (n + 1) → Bool) :
  v₁ = v₂ ↔ (v₁ 0 = v₂ 0) ∧ (Fin.tail v₁ = Fin.tail v₂) := by
  sorry -- Will complete proof later

theorem ult_zero (v₁ v₂ : Fin 0 → Bool) :
  v₁ < v₂ ↔ False := by
  sorry -- Will complete proof later

theorem ult_succ {n : Nat} (v₁ v₂ : Fin (n + 1) → Bool) :
  v₁ < v₂ ↔
  (Fin.tail v₁ < Fin.tail v₂) ∨ ((Fin.tail v₁ = Fin.tail v₂) ∧ (v₁ 0 = false) ∧ (v₂ 0 = true)) := by
  sorry -- Will complete proof later

end BV
