/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

/-!
# Counter

Typeclass for homomorphism to natural numbers.

This is used for allocating sequential IDs, with the assumption of an initial element
and an increment operator.

## Implementation notes

* Provides a way to allocate unique identifiers in sequence.
* The typeclass ensures a bijection with natural numbers via `toNat`.
* Some theorems use axioms for now - full proofs require additional structure.
-/

/-- Typeclass for types that can be used as sequential counters. -/
class Counter (α : Type _) where
  toNat : α → Nat
  init : α
  next : α → α
  next_toNat : ∀ (x : α), toNat (next x) = (toNat x) + 1
  init_toNat : toNat init = 0

namespace Counter
variable {α : Type _} [Counter α]

/-- Conversion from natural numbers. -/
def ofNat : Nat → α
  | 0 => init
  | n + 1 => next (ofNat n)

theorem to_ofNat (x : Nat) : toNat (ofNat x : α) = x := by
  induction x with
  | zero => simp only [ofNat, init_toNat]
  | succ n ih => simp only [ofNat, next_toNat, ih]

/-- toNat is injective (axiomatized for now). -/
axiom toNat_inj {x y : α} : toNat x = toNat y → x = y

theorem of_toNat (x : α) : ofNat (toNat x) = x := by
  apply toNat_inj
  rw [to_ofNat]

end Counter

/-- Natural numbers form a counter. -/
instance : Counter Nat where
  toNat := id
  init := 0
  next := Nat.succ
  next_toNat := by simp [id_eq]
  init_toNat := by simp [id_eq]
