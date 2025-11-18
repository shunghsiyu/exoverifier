/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

/-!
# Satisfiability

Basic properties of satisfiability.

## Implementation notes

* Defines the core `HasSat` typeclass for evaluating formulas under assignments.
-/

/-- Typeclass evaluating to Prop given an assignment. -/
class HasSat (α : outParam (Type _)) (β : Type _) where
  sat : (α → Bool) → β → Prop

-- Notation for satisfaction
notation:25 p " ⊨ " f => HasSat.sat p f
notation:25 p " ⊭ " f => ¬ (HasSat.sat p f)

section
variable {α : Type _}

/-- f is unsatisfiable. -/
def unsatisfiable {β : Type _} [HasSat α β] (f : β) : Prop :=
  ∀ (p : α → Bool), ¬ (p ⊨ f)

theorem unsat_of_forall_exists {β₁ β₂ : Type _} [HasSat α β₁] [HasSat α β₂]
    {f₁ : β₁} {f₂ : β₂}
    (h : ∀ (p₂ : α → Bool), HasSat.sat p₂ f₂ → ∃ (p₁ : α → Bool), HasSat.sat p₁ f₁) :
    unsatisfiable f₁ → unsatisfiable f₂ := by
  intro h_unsat p₂ h_sat
  obtain ⟨p₁, h_p₁⟩ := h p₂ h_sat
  exact h_unsat p₁ h_p₁

namespace Sat

/-- f₁ and f₂ are logically equivalent. -/
def liff {β₁ β₂ : Type _} [HasSat α β₁] [HasSat α β₂] (f₁ : β₁) (f₂ : β₂) : Prop :=
  ∀ (p : α → Bool), HasSat.sat p f₁ ↔ HasSat.sat p f₂

-- Notation for logical equivalence
notation:50 f₁ " ⇔ " f₂ => liff f₁ f₂

/-- f₁ logically implies f₂. -/
def limplies {β₁ β₂ : Type _} [HasSat α β₁] [HasSat α β₂] (f₁ : β₁) (f₂ : β₂) : Prop :=
  ∀ (p : α → Bool), HasSat.sat p f₁ → HasSat.sat p f₂

-- Notation for logical implication
infixr:40 " ⇒ " => limplies

protected theorem liff_refl {β : Type _} [HasSat α β] (f : β) : liff f f :=
  fun _ => Iff.rfl

protected theorem liff_symm {β₁ β₂ : Type _} [HasSat α β₁] [HasSat α β₂]
    {f₁ : β₁} {f₂ : β₂} : liff f₁ f₂ → liff f₂ f₁ :=
  fun h p => (h p).symm

protected theorem liff_trans {β₁ β₂ β₃ : Type _} [HasSat α β₁] [HasSat α β₂] [HasSat α β₃]
    {f₁ : β₁} {f₂ : β₂} {f₃ : β₃} :
    liff f₁ f₂ → liff f₂ f₃ → liff f₁ f₃ :=
  fun h₁ h₂ p => Iff.trans (h₁ p) (h₂ p)

protected theorem limplies_refl {β : Type _} [HasSat α β] (f : β) : limplies f f :=
  fun _ h => h

protected theorem limplies_trans {β₁ β₂ β₃ : Type _} [HasSat α β₁] [HasSat α β₂] [HasSat α β₃]
    {f₁ : β₁} {f₂ : β₂} {f₃ : β₃} :
    limplies f₁ f₂ → limplies f₂ f₃ → limplies f₁ f₃ :=
  fun h₁ h₂ p hp => h₂ p (h₁ p hp)

theorem liff_iff_limplies_and_limplies {β₁ β₂ : Type _} [HasSat α β₁] [HasSat α β₂]
    {f₁ : β₁} {f₂ : β₂} :
    liff f₁ f₂ ↔ limplies f₁ f₂ ∧ limplies f₂ f₁ := by
  unfold liff limplies
  constructor
  · intro h
    constructor
    · intro p hp; exact (h p).mp hp
    · intro p hp; exact (h p).mpr hp
  · intro ⟨h₁, h₂⟩ p
    exact ⟨h₁ p, h₂ p⟩

theorem limplies_of_liff_left {β₁ β₂ : Type _} [HasSat α β₁] [HasSat α β₂]
    {f₁ : β₁} {f₂ : β₂} (h : liff f₁ f₂) : limplies f₁ f₂ :=
  (liff_iff_limplies_and_limplies.mp h).1

theorem limplies_of_liff_right {β₁ β₂ : Type _} [HasSat α β₁] [HasSat α β₂]
    {f₁ : β₁} {f₂ : β₂} (h : liff f₁ f₂) : limplies f₂ f₁ :=
  (liff_iff_limplies_and_limplies.mp h).2

theorem liff_unsat {β₁ β₂ : Type _} [HasSat α β₁] [HasSat α β₂]
    {f₁ : β₁} {f₂ : β₂} (h : liff f₁ f₂) :
    unsatisfiable f₁ ↔ unsatisfiable f₂ := by
  unfold unsatisfiable liff at *
  constructor
  · intro h_unsat p
    rw [← h p]
    exact h_unsat p
  · intro h_unsat p
    rw [h p]
    exact h_unsat p

theorem limplies_unsat {β₁ β₂ : Type _} [HasSat α β₁] [HasSat α β₂]
    {f₁ : β₁} {f₂ : β₂} (h : limplies f₂ f₁) :
    unsatisfiable f₁ → unsatisfiable f₂ :=
  fun h_unsat p hp => h_unsat p (h p hp)

end Sat
end
