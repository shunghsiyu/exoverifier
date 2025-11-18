/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

/-!
# Hashable

Typeclass for hashing values to natural numbers.

## Implementation notes

* Original Lean 3 version used `pos_num`, but we use `Nat` in Lean 4 for simplicity.
* `PerfectHashable` provides an injective hash function.
* We define our own `ExoHashable` to avoid conflicts with Lean 4's built-in `Hashable`.
-/

/-- Typeclass for hashing values to natural numbers. -/
class ExoHashable (α : Type _) where
  hash : α → Nat

/-- Typeclass for perfect (injective) hashing. -/
class PerfectHashable (α : Type _) extends ExoHashable α where
  hash_inj : ∀ {x y : α}, hash x = hash y ↔ x = y

/-- Natural numbers are perfectly hashable via identity. -/
instance : PerfectHashable Nat where
  hash := id
  hash_inj := by
    intro x y
    simp only [id_eq]

/-- Booleans are perfectly hashable. -/
instance : PerfectHashable Bool where
  hash b := if b then 1 else 2
  hash_inj := by
    intro x y
    cases x <;> cases y <;> simp
