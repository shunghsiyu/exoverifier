/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Misc.List

/-!
# Fixed-size bitvectors

This file defines fixed-sized bitvectors following the SMT-LIB standard.

## Implementation notes

* `Fin n → Bool` is chosen as the data type, as it doesn't assume the order of bits.

* Map `Fin n → Bool` to `Fin (2^n)` to reuse its theorems.

## References

* http://smtlib.cs.uiowa.edu/Theories/FixedSizeBitVectors.smt2
* http://smtlib.cs.uiowa.edu/Logics/QF_BV.smt2
-/

namespace BV

section repr
variable {n : Nat}

instance : Repr (Fin n → Bool) where
  reprPrec v _ := "0b" ++ String.mk ((List.ofFn fun i => if v i then '1' else '0').reverse)

end repr

section conversion
variable {n : Nat}

/-- Convert bit-vector to nat. -/
def toNat (v : Fin n → Bool) : Nat :=
  (List.ofFn fun i => (if v i then 1 else 0) * 2^(i : Nat)).sum

@[simp]
theorem toNat_zero_width (v : Fin 0 → Bool) :
  toNat v = 0 := by
  simp [toNat]

theorem toNat_lt (v : Fin n → Bool) :
  toNat v < 2^n := by
  sorry -- Will complete proof later

/-- Convert nat to bit-vector -/
def ofNat (a : Nat) : Fin n → Bool :=
  fun i => a.testBit i

-- Simplified for now - will add more theorems as needed
theorem toNat_inj (v₁ v₂ : Fin n → Bool) :
  toNat v₁ = toNat v₂ ↔ v₁ = v₂ := by
  sorry -- Will complete proof later

/-- Extract the most-significant bit. -/
@[reducible]
def msb : ∀ {n : Nat}, (Fin n → Bool) → Bool
  | 0,     _ => false
  | n + 1, v => v (Fin.last n)

end conversion

/-! ### Constants -/
section const
variable {n : Nat}

/-- All bits false -/
def allFalse : Fin n → Bool := fun _ => false

/-- All bits true -/
def allTrue : Fin n → Bool := fun _ => true

instance instZeroBV : Zero (Fin n → Bool) where
  zero := allFalse

instance instOneBV : One (Fin n → Bool) where
  one := ofNat 1

@[simp]
theorem zero_eq : (0 : Fin n → Bool) = allFalse := rfl

end const

/-! ### Bitwise operators -/
section bitwise
variable {n : Nat}

/-- Bitwise `not`. -/
protected def not (v : Fin n → Bool) : Fin n → Bool :=
  fun i => !v i

/-- Bitwise `and`. -/
protected def and (v₁ v₂ : Fin n → Bool) : Fin n → Bool :=
  fun i => v₁ i && v₂ i

/-- Bitwise `or`. -/
protected def or (v₁ v₂ : Fin n → Bool) : Fin n → Bool :=
  fun i => v₁ i || v₂ i

/-- Bitwise `xor`. -/
protected def xor (v₁ v₂ : Fin n → Bool) : Fin n → Bool :=
  fun i => xor (v₁ i) (v₂ i)

@[simp]
theorem not_not (v : Fin n → Bool) :
  BV.not (BV.not v) = v := by
  funext i
  simp [BV.not]

@[simp]
theorem and_comm (v₁ v₂ : Fin n → Bool) :
  BV.and v₁ v₂ = BV.and v₂ v₁ := by
  funext i
  simp [BV.and, Bool.and_comm]

@[simp]
theorem or_comm (v₁ v₂ : Fin n → Bool) :
  BV.or v₁ v₂ = BV.or v₂ v₁ := by
  funext i
  simp [BV.or, Bool.or_comm]

end bitwise

end BV
