/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Misc.List

/-!
# Fixed-size bitvectors

This file defines fixed-sized bitvectors following the SMT-LIB standard.

## Implementation notes

* `Fin n → Bool` is chosen as the data type, as it doesn't assume the order of bits.

* Map `Fin n → Bool` to `Fin (2^n)` to reuse its theorems, as the latter forms a commutative ring.

## References

* http://smtlib.cs.uiowa.edu/Theories/FixedSizeBitVectors.smt2
* http://smtlib.cs.uiowa.edu/Logics/QF_BV.smt2
-/

namespace Bv

section repr
variable {n : ℕ}

instance : Repr (Fin n → Bool) where
  reprPrec v _ := "0b" ++ (List.ofFn (fun i => cond (v i) '1' '0')).reverse.asString

end repr

section conversion
variable {n : ℕ}

/-- Convert bit-vector to nat. -/
def toNat (v : Fin n → Bool) : ℕ :=
  (List.ofFn (fun i => cond (v i) 1 0 * 2^(i : ℕ))).sum

theorem toNat_cons (b : Bool) (v : Fin n → Bool) :
    toNat (Fin.cons b v) = (toNat v).bit b := by
  sorry

theorem toNat_snoc (v : Fin n → Bool) (b : Bool) :
    toNat (Fin.snoc v b) = toNat v + 2^n * cond b 1 0 := by
  sorry

theorem toNat_succ (v : Fin n.succ → Bool) :
    toNat v = (toNat (Fin.tail v)).bit (v 0) := by
  sorry

@[simp]
theorem pow_two_sub_add_cancel :
    2^n - 1 + 1 = 2^n := by
  omega

@[simp]
theorem pow_two_succ_sub_add_cancel :
    2^n.succ - 2 + 1 = 2^n.succ - 1 := by
  omega

theorem toNat_le (v : Fin n → Bool) :
    toNat v ≤ 2^n - 1 := by
  sorry

theorem toNat_lt (v : Fin n → Bool) :
    toNat v < 2^n := by
  have h := toNat_le v
  omega

@[simp]
theorem toNat_zero (v : Fin 0 → Bool) :
    toNat v = 0 := by
  simp [toNat]

theorem toNat_init (v : Fin (n + 1) → Bool) :
    toNat (Fin.init v) = toNat v % 2^n := by
  sorry

theorem toNat_tail (v : Fin (n + 1) → Bool) :
    toNat (Fin.tail v) = (toNat v).div2 := by
  sorry

/-- Convert an `n`-bit bitvector to `Fin (2^n)`. -/
def toFin (v : Fin n → Bool) : Fin (2^n - 1 + 1) :=
  ⟨toNat v, Nat.lt_succ_of_le (toNat_le _)⟩

/-- Convert nat to bit-vector -/
def ofNat (a : ℕ) : Fin n → Bool :=
  fun i => a.testBit i

@[simp]
theorem of_toNat (v : Fin n → Bool) :
    ofNat (toNat v) = v := by
  sorry

theorem toNat_inj (v₁ v₂ : Fin n → Bool) :
    toNat v₁ = toNat v₂ ↔ v₁ = v₂ := by
  constructor
  · intro h
    have : ofNat (toNat v₁) = ofNat (toNat v₂) := by rw [h]
    simp at this
    exact this
  · intro h
    rw [h]

theorem eq_of_toNat_eq_toNat {v₁ v₂ : Fin n → Bool} :
    toNat v₁ = toNat v₂ → v₁ = v₂ :=
  (toNat_inj v₁ v₂).1

theorem eq_of_toFin_eq_toFin {v₁ v₂ : Fin n → Bool} :
    toFin v₁ = toFin v₂ → v₁ = v₂ := by
  intro h
  apply eq_of_toNat_eq_toNat
  have : (toFin v₁).val = (toFin v₂).val := by rw [h]
  exact this

theorem toNat_eq_of_heq {n₁ n₂ : ℕ} {v₁ : Fin n₁ → Bool} {v₂ : Fin n₂ → Bool} :
    n₁ = n₂ → HEq v₁ v₂ → toNat v₁ = toNat v₂ := by
  intro h₁ h₂
  subst h₁
  rw [heq_iff_eq] at h₂
  subst h₂

theorem ofNat_succ (a : ℕ) :
    (ofNat a : Fin n.succ → Bool) = Fin.cons (a % 2 = 1) (ofNat a.div2) := by
  sorry

theorem to_ofNat : ∀ (a : ℕ), toNat (@ofNat n a) = a % 2^n := by
  sorry

end conversion

def msb : ∀ {n : ℕ}, (Fin n → Bool) → Bool
  | 0, _ => false
  | _ + 1, v => v (Fin.last _)

section const
variable {n : ℕ}

instance : Bot (Fin n → Bool) where
  bot := fun _ => false

instance : Top (Fin n → Bool) where
  top := fun _ => true

instance : Zero (Fin n → Bool) where
  zero := ofNat 0

instance : One (Fin n → Bool) where
  one := ofNat 1

theorem bot_toNat : toNat (⊥ : Fin n → Bool) = 0 := by
  sorry

theorem top_toNat : toNat (⊤ : Fin n → Bool) = 2^n - 1 := by
  sorry

theorem zero_toNat : toNat (0 : Fin n → Bool) = 0 := by
  sorry

theorem zero_toFin : toFin (0 : Fin n → Bool) = 0 := by
  sorry

theorem one_toNat : toNat (1 : Fin n → Bool) = 1 % 2^n := by
  sorry

theorem one_toFin : toFin (1 : Fin n → Bool) = 1 % (2^n - 1 + 1) := by
  sorry

end const

section bitwise
variable {n : ℕ}

instance : Complement (Fin n → Bool) where
  complement v := fun i => !v i

instance : Inf (Fin n → Bool) where
  inf v₁ v₂ := fun i => v₁ i && v₂ i

instance : Sup (Fin n → Bool) where
  sup v₁ v₂ := fun i => v₁ i || v₂ i

-- Note: Boolean algebra instances need detailed proofs
-- Placeholder for now

theorem not_toNat (v : Fin n → Bool) :
    toNat (vᶜ) = 2^n - 1 - toNat v := by
  sorry

end bitwise

section arithmetic
variable {n : ℕ}

instance : Add (Fin n → Bool) where
  add v₁ v₂ := ofNat (toNat v₁ + toNat v₂)

instance : Neg (Fin n → Bool) where
  neg v := ofNat (2^n - toNat v)

instance : Mul (Fin n → Bool) where
  mul v₁ v₂ := ofNat (toNat v₁ * toNat v₂)

theorem add_toFin (v₁ v₂ : Fin n → Bool) :
    toFin (v₁ + v₂) = toFin v₁ + toFin v₂ := by
  sorry

theorem neg_toFin (v : Fin n → Bool) :
    toFin (-v) = -toFin v := by
  sorry

theorem mul_toFin (v₁ v₂ : Fin n → Bool) :
    toFin (v₁ * v₂) = toFin v₁ * toFin v₂ := by
  sorry

-- Add more arithmetic operations as needed

end arithmetic

-- Additional sections (shifts, comparisons, etc.) to be added

end Bv
