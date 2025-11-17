/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Mathlib.Data.List.Basic

namespace List

theorem nth_append_eq_ite {α : Type*} {l r : List α} {i : ℕ} :
    (l ++ r)[i]? = if (i < l.length) then l[i]? else r[i - l.length]? := by
  split_ifs with h
  · rw [getElem?_append]
    simp [h]
  · rw [getElem?_append_right]
    push_neg at h
    exact Nat.le_of_not_lt h

section subset
variable {α : Type*}

theorem subset_cons_iff_subset {a : α} {l₁ l₂ : List α} (h : a ∉ l₁) :
    l₁ ⊆ (a :: l₂) ↔ l₁ ⊆ l₂ := by
  simp only [subset_def, mem_cons]
  constructor
  · intro h' a' a'l₁
    specialize h' a'l₁
    cases h' with
    | inl h' => subst h'; contradiction
    | inr h' => exact h'
  · intro h' a' a'l₁
    right
    exact h' a'l₁

theorem subset_append_iff_subset_left {l₁ l₂ l₃ : List α} (d : Disjoint l₁ l₃) :
    l₁ ⊆ l₂ ++ l₃ ↔ l₁ ⊆ l₂ := by
  simp only [subset_def, mem_append]
  constructor
  · intro h a al₁
    specialize h al₁
    cases h with
    | inl h => exact h
    | inr h => exfalso; exact d.symm.forall_ne_finset a al₁ h rfl
  · intro h a al₁
    left
    exact h al₁

theorem subset_append_iff_subset_right {l₁ l₂ l₃ : List α} (d : Disjoint l₁ l₂) :
    l₁ ⊆ l₂ ++ l₃ ↔ l₁ ⊆ l₃ := by
  simp only [subset_def, mem_append]
  constructor
  · intro h a al₁
    specialize h al₁
    cases h with
    | inl h => exfalso; exact d.forall_ne_finset a al₁ h rfl
    | inr h => exact h
  · intro h a al₁
    right
    exact h al₁

end subset

namespace sigma
variables {α : Type*} [DecidableEq α] {β : α → Type*}

def find (x : α) (p : β x → Prop) [DecidablePred p] : List (Sigma β) → Option (β x)
  | [] => none
  | (⟨x', v⟩ :: xs) =>
    if h : x' = x then
      let v' : β x := h ▸ v
      if p v' then v' else find xs
    else find xs

theorem find_some {x : α} {p : β x → Prop} [DecidablePred p] {l : List (Sigma β)} {v : β x}
    (H : find x p l = some v) : p v := by
  induction l with
  | nil => cases H
  | cons hd tl ih =>
    cases hd with | mk x' v' =>
    simp [find] at H
    split_ifs at H
    · subst_vars
      cases H
      assumption
    · exact ih H

theorem find_mem {x : α} {p : β x → Prop} [DecidablePred p] {l : List (Sigma β)} {v : β x}
    (H : find x p l = some v) : Sigma.mk x v ∈ l := by
  induction l with
  | nil => cases H
  | cons hd tl ih =>
    rw [mem_cons]
    cases hd with | mk x' v' =>
    simp [find] at H
    split_ifs at H
    · subst_vars
      cases H
      left; rfl
    · right; exact ih H

end sigma

-- Note: Lean 4's metaprogramming system is different from Lean 3
-- The has_to_pexpr functionality would need to be reimplemented using Lean 4's reflection
-- Commenting out for now
-- section has_to_pexpr
-- variables {α : Type*} [has_to_pexpr α]
-- private meta def to_pexpr' : List α → pexpr
-- | nil      := ``(nil)
-- | (hd::tl) := ``(cons %%hd %%(to_pexpr' tl))
-- meta instance : has_to_pexpr (List α) := ⟨to_pexpr'⟩
-- end has_to_pexpr

end List
