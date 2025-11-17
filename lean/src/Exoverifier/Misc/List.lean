/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

namespace List

-- Note: getElem?_append_left and getElem?_append_right already exist in Lean 4

section subset
variable {α : Type _}

theorem subset_cons_iff_subset {a : α} {l₁ l₂ : List α} (h : a ∉ l₁) :
  l₁ ⊆ (a :: l₂) ↔ l₁ ⊆ l₂ := by
  simp only [List.subset_def, List.mem_cons]
  constructor
  · intro h' a' a'l₁
    specialize h' a'l₁
    cases h' with
    | inl heq => subst heq; contradiction
    | inr hmem => exact hmem
  · intro h' a' a'l₁
    right
    exact h' a'l₁

-- Disjoint in Lean 4 is defined differently, let's use a custom definition
def Disjoint' (l₁ l₂ : List α) : Prop :=
  ∀ a, a ∈ l₁ → a ∈ l₂ → False

theorem subset_append_iff_subset_left {l₁ l₂ l₃ : List α} (d : Disjoint' l₁ l₃) :
  l₁ ⊆ l₂ ++ l₃ ↔ l₁ ⊆ l₂ := by
  simp only [List.subset_def, List.mem_append]
  constructor
  · intro h a al₁
    specialize h al₁
    cases h with
    | inl hmem => exact hmem
    | inr hmem =>
      unfold Disjoint' at d
      have := d a al₁ hmem
      contradiction
  · intro h a al₁
    left
    exact h al₁

theorem subset_append_iff_subset_right {l₁ l₂ l₃ : List α} (d : Disjoint' l₁ l₂) :
  l₁ ⊆ l₂ ++ l₃ ↔ l₁ ⊆ l₃ := by
  simp only [List.subset_def, List.mem_append]
  constructor
  · intro h a al₁
    specialize h al₁
    cases h with
    | inl hmem =>
      unfold Disjoint' at d
      have := d a al₁ hmem
      contradiction
    | inr hmem => exact hmem
  · intro h a al₁
    right
    exact h al₁

end subset

namespace Sigma

def find {α : Type _} [DecidableEq α] {β : α → Type _}
    (x : α) (p : β x → Prop) [DecidablePred p] : List (Sigma β) → Option (β x)
  | [] => none
  | ⟨x', v⟩ :: xs =>
    if h : x' = x then
      let v' : β x := h ▸ v
      if p v' then some v' else find x p xs
    else find x p xs

theorem find_some {α : Type _} [DecidableEq α] {β : α → Type _}
    {x : α} {p : β x → Prop} [DecidablePred p] {l : List (Sigma β)} {v : β x}
    (H : find x p l = some v) : p v := by
  induction l with
  | nil => cases H
  | cons hd tl ih =>
    cases hd with | mk x' v' =>
    simp [find] at H
    split at H
    · next h =>
      split at H
      · next hpv =>
        cases H
        exact hpv
      · exact ih H
    · exact ih H

theorem find_mem {α : Type _} [DecidableEq α] {β : α → Type _}
    {x : α} {p : β x → Prop} [DecidablePred p] {l : List (Sigma β)} {v : β x}
    (H : find x p l = some v) : Sigma.mk x v ∈ l := by
  induction l with
  | nil => cases H
  | cons hd tl ih =>
    simp [List.mem_cons]
    cases hd with | mk x' v' =>
    simp [find] at H
    split at H
    · next h =>
      split at H
      · next hpv =>
        cases H
        left
        subst h
        simp
      · right; exact ih H
    · right; exact ih H

end Sigma

-- Note: Meta programming (has_to_pexpr) omitted, can be added if needed

end List
