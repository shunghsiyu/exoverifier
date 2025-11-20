/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Mathlib.Data.List.Sigma

/-!
# Unordered Maps

Type class for unordered map data structures, providing a common interface
for various implementations.
-/

/-- Typeclass for unordered maps. -/
class UnorderedMap (α β : outParam Type _) (σ : Type _) where
  to_list : σ → List (Σ _ : α, β)
  nodupkeys : ∀ (m : σ), (to_list m).Nodup<|end_of_text|>Keys
  elems : σ → List β
  mem_elems_iff : ∀ (m : σ) (b : β), b ∈ elems m ↔ ∃ (a : α), Sigma.mk a b ∈ to_list m
  empty : σ
  empty_eq : to_list empty = []
  null : σ → Bool
  null_iff : ∀ (m : σ),
    null m ↔ to_list m = []
  unsingleton : σ → Option (Σ _ : α, β)
  unsingleton_iff : ∀ (m : σ) (s : (Σ _ : α, β)),
    unsingleton m = some s ↔ to_list m = [s]
  card : σ → Nat
  card_eq : ∀ (m : σ),
    card m = (to_list m).length
  lookup [DecidableEq α] : α → σ → Option β
  mem_lookup_iff [DecidableEq α] : ∀ (a : α) (b : β) (m : σ),
    b ∈ lookup a m ↔ Sigma.mk a b ∈ to_list m
  kinsert [DecidableEq α] : α → β → σ → σ
  mem_kinsert_iff [DecidableEq α] : ∀ (a : α) (b : β) (m : σ) (s : (Σ _ : α, β)),
    s ∈ to_list (kinsert a b m) ↔ s ∈ to_list m ∨ (a ∉ (to_list m).keys ∧ s = ⟨a, b⟩)
  insert₂ [DecidableEq α] [DecidableEq β] : α → β → σ → σ
  mem_insert₂_iff [DecidableEq α] [DecidableEq β] : ∀ (a : α) (b : β) (m : σ) (s : (Σ _ : α, β)),
    s ∈ to_list (insert₂ a b m) ↔
    (s = ⟨a, b⟩ ∨ s ∈ to_list m) ∧ (a ∈ (to_list m).keys → Sigma.mk a b ∈ to_list m)
  kerase [DecidableEq α] : σ → α → σ
  mem_kerase_iff [DecidableEq α] : ∀ (m : σ) (a : α) (s : (Σ _ : α, β)),
    s ∈ to_list (kerase m a) ↔ s.1 ≠ a ∧ s ∈ to_list m
  erase₂ [DecidableEq α] [DecidableEq β] : σ → α → β → σ
  mem_erase₂_iff [DecidableEq α] [DecidableEq β] : ∀ (m : σ) (a : α) (b : β) (s : (Σ _ : α, β)),
    s ∈ to_list (erase₂ m a b) ↔ s ≠ ⟨a, b⟩ ∧ s ∈ to_list m
  filter_map : (β → Option β) → σ → σ
  mem_filter_map_iff (f : β → Option β) : ∀ (m : σ) (s : (Σ _ : α, β)),
    s ∈ to_list (filter_map f m) ↔ ∃ b, (⟨s.1, b⟩ : (Σ _ : α, β)) ∈ to_list m ∧ f b = some s.2
  ksdiff [DecidableEq α] : σ → σ → σ
  mem_ksdiff_iff [DecidableEq α] : ∀ (m₁ m₂ : σ) (s : (Σ _ : α, β)),
    s ∈ to_list (ksdiff m₁ m₂) ↔ s ∈ to_list m₁ ∧ s.1 ∉ (to_list m₂).keys
  union₂ [DecidableEq α] [DecidableEq β] : σ → σ → Option σ
  mem_union₂_iff [DecidableEq α] [DecidableEq β] : ∀ (m₁ m₂ : σ) (s : (Σ _ : α, β)),
    (∃ (m : σ), union₂ m₁ m₂ = some m ∧ s ∈ to_list m) ↔
    (s ∈ to_list m₁ ∨ s ∈ to_list m₂) ∧ ∀ (a : α) (b₁ b₂ : β),
      Sigma.mk a b₁ ∈ to_list m₁ → Sigma.mk a b₂ ∈ to_list m₂ → b₁ = b₂
  sdiff₂ [DecidableEq α] [DecidableEq β] : σ → σ → σ
  mem_sdiff₂_iff [DecidableEq α] [DecidableEq β] : ∀ (m₁ m₂ : σ) (s : (Σ _ : α, β)),
    s ∈ to_list (sdiff₂ m₁ m₂) ↔ s ∈ to_list m₁ ∧ s ∉ to_list m₂
  insert_with [DecidableEq α] :
    (β → β → β) → α → β → σ → σ

namespace UnorderedMap
variable {α β σ : Type _} [UnorderedMap α β σ]

def ofList [DecidableEq α] : List (Σ (_ : α), β) → σ
  | []             => empty
  | ⟨k, v⟩ :: xs => kinsert k v (ofList xs)

lemma mem_of_lookup_is_some [DecidableEq α] {a : α} {m : σ} (h : (lookup a m).isSome) :
    Sigma.mk a (Option.get h) ∈ to_list m := by
  simp [← mem_lookup_iff]

def kerase_all [DecidableEq α] (m : σ) (as : List α) : σ :=
  as.foldl kerase m

lemma mem_kerase_all_iff [DecidableEq α] (m : σ) (as : List α) (s : (Σ _ : α, β)) :
    s ∈ to_list (kerase_all m as) ↔ s.1 ∉ as ∧ s ∈ to_list m := by
  revert m
  simp only [kerase_all]
  induction as with
  | nil => simp
  | cons a as ih =>
    intro m
    simp only [List.foldl, List.mem_cons]
    rw [ih, mem_kerase_iff]
    tauto

lemma kerase_all_subset [DecidableEq α] (m : σ) (as : List α) :
    to_list (kerase_all m as) ⊆ to_list m :=
  fun _ => by rw [mem_kerase_all_iff]; tauto

lemma ksdiff_all_subset [DecidableEq α] (m₁ m₂ : σ) :
    to_list (ksdiff m₁ m₂) ⊆ to_list m₁ :=
  fun _ => by rw [mem_ksdiff_iff]; tauto

lemma subset_of_sdiff₂_null [DecidableEq α] [DecidableEq β] {m₁ m₂ : σ} :
    null (sdiff₂ m₁ m₂) →
    to_list m₁ ⊆ to_list m₂ := by
  simp only [null_iff, List.eq_nil_iff_forall_not_mem, mem_sdiff₂_iff]
  intro h l
  specialize h l
  tauto

end UnorderedMap

universe u
open UnorderedMap

/-- Maps that can operate on any value type. -/
class GenericMap (α : outParam Type _) (σ : Type u → Type u) where
  to_map                : ∀ {β : Type u}, UnorderedMap α β (σ β)
  to_traversable        : Traversable σ
  to_lawful_traversable : LawfulTraversable σ
  filter_map          : ∀ {β₁ β₂ : Type u},
    (β₁ → Option β₂) → σ β₁ → σ β₂
  mem_filter_map_iff  : ∀ {β₁ β₂ : Type u} {f : β₁ → Option β₂} {m₁ : σ β₁} {s : Σ (_ : α), β₂},
    s ∈ to_list (filter_map f m₁) ↔
    (∃ (b₁ : β₁),
      (⟨s.1, b₁⟩ : Σ (_ : α), β₁) ∈ to_list m₁ ∧
      f b₁ = some s.2)
  filter_map₂         : ∀ {β₁ β₂ β₃ : Type u},
    (β₁ → β₂ → Option β₃) → σ β₁ → σ β₂ → Option (σ β₃)
  mem_filter_map₂_iff : ∀ {β₁ β₂ β₃ : Type u} {f : β₁ → β₂ → Option β₃} {m₁ : σ β₁} {m₂ : σ β₂} {s : Σ (_ : α), β₃},
    (∃ (m₃ : σ β₃), filter_map₂ f m₁ m₂ = some m₃ ∧ s ∈ to_list m₃) ↔
    (∃ (b₁ : β₁) (b₂ : β₂),
      (⟨s.1, b₁⟩ : Σ (_ : α), β₁) ∈ to_list m₁ ∧
      (⟨s.1, b₂⟩ : Σ (_ : α), β₂) ∈ to_list m₂ ∧
      f b₁ b₂ = some s.2) ∧
    (to_list m₁).keys ⊆ (to_list m₂).keys

-- Export instances for generic_map
attribute [instance]
  GenericMap.to_map
  GenericMap.to_traversable
  GenericMap.to_lawful_traversable
