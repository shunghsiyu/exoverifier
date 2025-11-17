/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.BV.Adc

namespace BV

variable {n : Nat}

/-- Subtract with carry (borrow). -/
protected def sbc (v₁ v₂ : Fin n → Bool) (c : Bool) : Fin n → Bool :=
  v₁ - v₂ - if c then 0 else 1

/-- Overflow checking for subtract with carry. -/
def sbcOverflow (v₁ v₂ : Fin n → Bool) (c : Bool) : Prop :=
  toNat v₁ < toNat v₂ + if c then 0 else 1

instance : ∀ (v₁ v₂ : Fin n → Bool) (c : Bool), Decidable (sbcOverflow v₁ v₂ c) :=
  fun _ _ _ => by unfold sbcOverflow; infer_instance

theorem sbc_eq_adc (v₁ v₂ : Fin n → Bool) (c : Bool) :
  BV.sbc v₁ v₂ c = BV.adc v₁ (BV.not v₂) c := by
  sorry -- Will complete proof later

theorem sbcOverflow_iff_not_adcOverflow (v₁ v₂ : Fin n → Bool) (c : Bool) :
  sbcOverflow v₁ v₂ c ↔ ¬ adcOverflow v₁ (BV.not v₂) c := by
  sorry -- Will complete proof later

theorem sub_eq_sbc (v₁ v₂ : Fin n → Bool) :
  v₁ - v₂ = BV.sbc v₁ v₂ true := by
  sorry -- Will complete proof later

end BV
