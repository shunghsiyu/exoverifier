/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.BV.Basic

namespace Fin

/-- Extract all elements except the first one (index 0). -/
def tail {α : Type _} (v : Fin (n + 1) → α) : Fin n → α :=
  fun i => v i.succ

end Fin

namespace BV

variable {n : Nat}

/-- Add with carry. -/
protected def adc (v₁ v₂ : Fin n → Bool) (c : Bool) : Fin n → Bool :=
  v₁ + v₂ + if c then 1 else 0

/-- Overflow checking for add with carry. -/
def adcOverflow (v₁ v₂ : Fin n → Bool) (c : Bool) : Prop :=
  2^n ≤ toNat v₁ + toNat v₂ + if c then 1 else 0

instance : ∀ (v₁ v₂ : Fin n → Bool) (c : Bool), Decidable (adcOverflow v₁ v₂ c) :=
  fun _ _ _ => by unfold adcOverflow; infer_instance

theorem adc_eq_ofNat (v₁ v₂ : Fin n → Bool) (c : Bool) :
  BV.adc v₁ v₂ c = ofNat (toNat v₁ + toNat v₂ + if c then 1 else 0) := by
  sorry -- Will complete proof later

theorem adc_zero (v₁ v₂ : Fin (n + 1) → Bool) (c : Bool) :
  BV.adc v₁ v₂ c 0 = xor (xor (v₁ 0) (v₂ 0)) c := by
  sorry -- Will complete proof later

theorem adc_succ (v₁ v₂ : Fin (n + 1) → Bool) (c : Bool) : ∀ i,
  BV.adc v₁ v₂ c (Fin.succ i) =
  BV.adc (Fin.tail v₁) (Fin.tail v₂) (((v₁ 0) && (v₂ 0)) || (c && (xor (v₁ 0) (v₂ 0)))) i := by
  sorry -- Will complete proof later

theorem adcOverflow_succ (v₁ v₂ : Fin (n + 1) → Bool) (c : Bool) :
  adcOverflow v₁ v₂ c ↔
  adcOverflow (Fin.tail v₁) (Fin.tail v₂) (v₁ 0 && v₂ 0 || c && xor (v₁ 0) (v₂ 0)) := by
  sorry -- Will complete proof later

theorem add_eq_adc (v₁ v₂ : Fin n → Bool) :
  v₁ + v₂ = BV.adc v₁ v₂ false := by
  sorry -- Will complete proof later

end BV
