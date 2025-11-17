/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Basic
import Misc.List

namespace Fin
variable {n : ℕ} {α : Type*}

/-- Heterogeneous injectivity of List.ofFn. -/
theorem list_ofFn_inj_het {α : Type*} {n₁ n₂ : ℕ} {f₁ : Fin n₁ → α} {f₂ : Fin n₂ → α} :
    (List.ofFn f₁ = List.ofFn f₂) ↔ (n₁ = n₂ ∧ HEq f₁ f₂) := by
  constructor
  · intro h
    have length_match := congr_arg List.length h
    simp only [List.length_ofFn] at length_match
    subst length_match
    rw [heq_iff_eq]
    refine ⟨rfl, ?_⟩
    ext ⟨i, _⟩
    have : (List.ofFn f₁).get? i = (List.ofFn f₂).get? i := by rw [h]
    simp [List.ofFn_get?] at this
    exact this
  · intro ⟨h₁, h₂⟩
    subst h₁
    rw [heq_iff_eq] at h₂
    cases h₂
    rfl

/-- Homogeneous injectivity of List.ofFn -/
theorem list_ofFn_inj (v₁ v₂ : Fin n → α) : List.ofFn v₁ = List.ofFn v₂ ↔ v₁ = v₂ := by
  simp [list_ofFn_inj_het]

theorem list_ofFn_snoc {xs : Fin n → α} {x : α} :
    List.ofFn (Fin.snoc xs x : Fin (n + 1) → α) = List.ofFn xs ++ [x] := by
  ext i
  simp only [List.nth_append_eq_ite, List.ofFn_get?, List.length_ofFn]
  split_ifs with h
  · simp [Fin.snoc, h]
  · push_neg at h
    simp [Fin.snoc]
    omega

theorem cast_eq_rec {β : Type*} (f : ∀ {n : ℕ}, (Fin n → α) → β) {n' : ℕ} (h : n = n') (v : Fin n → α) :
    f (h ▸ v) = f v := by
  subst h
  rfl

section reverse

/-- Reverse a tuple. -/
def reverse (v : Fin n → α) : Fin n → α :=
  fun ⟨i, h⟩ => v ⟨n - i - 1, by omega⟩

theorem reverse_tail_eq_init_reverse (v : Fin (n + 1) → α) :
    reverse (tail v) = init (reverse v) := by
  ext ⟨_, _⟩
  simp only [init, castSucc_mk]
  simp only [reverse, tail, succ_mk]
  congr
  omega

theorem reverse_last_eq_head (v : Fin (n + 1) → α) :
    reverse v (Fin.last n) = v 0 := by
  simp only [Fin.last, reverse]
  congr
  omega

theorem reverse_reverse (v : Fin n → α) :
    reverse (reverse v) = v := by
  ext ⟨_, _⟩
  simp only [reverse]
  congr
  omega

theorem list_ofFn_reverse {f : Fin n → α} :
    List.ofFn (Fin.reverse f) = List.reverse (List.ofFn f) := by
  ext i
  simp only [List.ofFn_get?, List.length_ofFn, List.length_reverse]
  split_ifs with h
  · simp [reverse]
    -- This needs more detailed proof but structure is here
    sorry
  · simp

end reverse
end Fin
