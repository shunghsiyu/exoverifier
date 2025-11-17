/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

/-!
# Miscellaneous vector functions and lemmas

Lean 4's Vector is defined as `{ toArray : Array α // toArray.size = n }`
We add some additional utility functions and compatibility notation.
-/

namespace Vector

variable {α β γ : Type _} {n m : Nat}

/-- Initialize a vector. Take all but the last element. -/
def init (v : Vector α (n + 1)) : Vector α n :=
  ⟨v.toArray.pop, by simp [v.size_toArray]⟩

/-- Add an element at the end of a vector (snoc). -/
def snoc (v : Vector α n) (a : α) : Vector α (n + 1) :=
  ⟨v.toArray.push a, by simp [v.size_toArray]⟩

/-- Map a binary function over two vectors. -/
def map₂ (f : α → β → γ) (v₁ : Vector α n) (v₂ : Vector β n) : Vector γ n :=
  ⟨Array.zipWith f v₁.toArray v₂.toArray, by
    rw [Array.size_zipWith]
    simp [v₁.size_toArray, v₂.size_toArray]⟩

-- Basic theorems

theorem toList_length (v : Vector α n) :
  v.toList.length = n := by
  simp

theorem snoc_toList (v : Vector α n) (a : α) :
  (snoc v a).toList = v.toList ++ [a] := by
  simp [snoc, Vector.toList]

end Vector
