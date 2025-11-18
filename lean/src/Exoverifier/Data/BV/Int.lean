/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.BV.Basic

/-!
# Bitvectors and integers

This file provides lemmas between bitvectors and ℤ as sanity checks.
-/

namespace BV

variable {n : Nat}

/-- Convert an integer to a bitvector. -/
def ofInt (a : Int) : Fin n → Bool :=
  ofNat (a % (2^n : Int)).toNat

/-- Convert a bitvector to a signed integer. -/
def toInt (v : Fin n → Bool) : Int :=
  if toNat v < 2^(n - 1) then toNat v else toNat v - 2^n

theorem of_toInt (v : Fin n → Bool) :
  ofInt (toInt v) = v := by
  sorry -- Will complete proof later

theorem toInt_inj (v₁ v₂ : Fin n → Bool) :
  toInt v₁ = toInt v₂ ↔ v₁ = v₂ := by
  sorry -- Will complete proof later

@[simp]
theorem toInt_zero (v : Fin 0 → Bool) :
  toInt v = 0 := by
  simp [toInt]

theorem neg_toInt (v : Fin n → Bool) :
  toInt (-v) = if toInt v = -2^(n - 1) then -2^(n - 1) else -toInt v := by
  sorry -- Will complete proof later

theorem msb_eq_false_iff (v : Fin n → Bool) :
  msb v = false ↔ toNat v < 2^(n - 1) := by
  sorry -- Will complete proof later

theorem slt_toInt (v₁ v₂ : Fin n → Bool) :
  toInt v₁ < toInt v₂ ↔ BV.slt v₁ v₂ := by
  sorry -- Will complete proof later

theorem sle_toInt (v₁ v₂ : Fin n → Bool) :
  toInt v₁ ≤ toInt v₂ ↔ BV.sle v₁ v₂ := by
  sorry -- Will complete proof later

end BV
