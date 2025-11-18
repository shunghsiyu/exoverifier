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

/-! ### Arithmetic operations -/
section arithmetic
variable {n : Nat}

/-- Addition. -/
protected def add (v₁ v₂ : Fin n → Bool) : Fin n → Bool :=
  ofNat (toNat v₁ + toNat v₂)

/-- Negation. -/
protected def neg (v : Fin n → Bool) : Fin n → Bool :=
  ofNat (2^n - toNat v)

/-- Subtraction. -/
protected def sub (v₁ v₂ : Fin n → Bool) : Fin n → Bool :=
  ofNat (toNat v₁ + (2^n - toNat v₂))

/-- Multiplication. -/
protected def mul (v₁ v₂ : Fin n → Bool) : Fin n → Bool :=
  ofNat (toNat v₁ * toNat v₂)

instance instAddBV : Add (Fin n → Bool) where
  add := BV.add

instance instNegBV : Neg (Fin n → Bool) where
  neg := BV.neg

instance instSubBV : Sub (Fin n → Bool) where
  sub := BV.sub

instance instMulBV : Mul (Fin n → Bool) where
  mul := BV.mul

-- Basic theorems about arithmetic
theorem add_to_nat (v₁ v₂ : Fin n → Bool) :
  toNat (v₁ + v₂) = (toNat v₁ + toNat v₂) % 2^n := by
  sorry -- Will complete proof later

theorem mul_to_nat (v₁ v₂ : Fin n → Bool) :
  toNat (v₁ * v₂) = (toNat v₁ * toNat v₂) % 2^n := by
  sorry -- Will complete proof later

end arithmetic

/-! ### Shift and rotate operations -/
section shift
variable {n : Nat}

/-- Logical shift left. -/
protected def shl (v : Fin n → Bool) (k : Nat) : Fin n → Bool :=
  ofNat (toNat v * 2^k)

/-- Logical shift right. -/
protected def lshr (v : Fin n → Bool) (k : Nat) : Fin n → Bool :=
  ofNat (toNat v / 2^k)

/-- Arithmetic shift right (sign-extend). -/
protected def ashr (v : Fin n → Bool) (k : Nat) : Fin n → Bool :=
  if msb v then
    -- Sign bit is 1, fill with 1s
    BV.or (BV.lshr v k) (ofNat ((2^n - 1) - (2^(n - k) - 1)))
  else
    -- Sign bit is 0, same as logical shift
    BV.lshr v k

end shift

/-! ### Relational operators -/
section relational
variable {n : Nat}

/-- Unsigned less than. -/
protected def ult (v₁ v₂ : Fin n → Bool) : Prop :=
  toNat v₁ < toNat v₂

/-- Unsigned less than or equal. -/
protected def ule (v₁ v₂ : Fin n → Bool) : Prop :=
  toNat v₁ ≤ toNat v₂

instance : LT (Fin n → Bool) where
  lt := BV.ult

instance : LE (Fin n → Bool) where
  le := BV.ule

instance : DecidableRel (α := Fin n → Bool) (· < ·) :=
  fun v₁ v₂ => inferInstanceAs (Decidable (toNat v₁ < toNat v₂))

instance : DecidableRel (α := Fin n → Bool) (· ≤ ·) :=
  fun v₁ v₂ => inferInstanceAs (Decidable (toNat v₁ ≤ toNat v₂))

/-- Signed less than. -/
protected def slt (v₁ v₂ : Fin n → Bool) : Prop :=
  (msb v₁ = true ∧ msb v₂ = false) ∨ (msb v₁ = msb v₂ ∧ v₁ < v₂)

/-- Signed less than or equal. -/
protected def sle (v₁ v₂ : Fin n → Bool) : Prop :=
  (msb v₁ = true ∧ msb v₂ = false) ∨ (msb v₁ = msb v₂ ∧ v₁ ≤ v₂)

/-- Signed greater than. -/
@[reducible]
protected def sgt (v₁ v₂ : Fin n → Bool) : Prop :=
  BV.slt v₂ v₁

/-- Signed greater than or equal. -/
@[reducible]
protected def sge (v₁ v₂ : Fin n → Bool) : Prop :=
  BV.sle v₂ v₁

instance : DecidableRel (α := Fin n → Bool) BV.slt :=
  fun _ _ => by unfold BV.slt; infer_instance

instance : DecidableRel (α := Fin n → Bool) BV.sle :=
  fun _ _ => by unfold BV.sle; infer_instance

end relational

end BV
