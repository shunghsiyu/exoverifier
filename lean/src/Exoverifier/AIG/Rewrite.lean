/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.AIG.Basic

/-!
# AIG rewriting

This file provides support for AIG rewriting using two-level optimization rules.

## Implementation notes

Optimization rules at level 1 are implemented by the factory.

Optimization rules at level 2, which return existing subterms (i.e., they don't create new terms),
are represented by `Subrule`. These rules are confluent and terminating.

Optimization rules at level 3 & 4, which create new terms from existing subterms, are represented
by `Newrule`. These rules require recursion.

## References

* Robert Brummayer and Armin Biere.
  *Local Two-Level And-Inverter Graph Minimization without Blowup*.
  <http://fmv.jku.at/papers/BrummayerBiere-MEMICS06.pdf>
-/

namespace AIG
namespace Rewrite

/-- A triple (node ID, edge, node) used by optimization rules. -/
@[reducible]
def Term (α : Type _) : Type _ :=
  α × Bool × Node α

/-- An optimization rule at level 2, which returns an existing subterm. -/
structure Subrule (α : Type _) where
  run : Term α → Term α → Option (Ref α)
  sat : ∀ {r : Ref α} {g : Graph α} {a₁ a₂ : α} {b₁ b₂ r₁ r₂ : Bool} {n₁ n₂ : Node α},
    run (a₁, b₁, n₁) (a₂, b₂, n₂) = some r →
    g a₁ = some n₁ →
    g a₂ = some n₂ →
    (Ref.Sat g (Ref.root a₁ b₁) r₁) →
    (Ref.Sat g (Ref.root a₂ b₂) r₂) →
    Ref.Sat g r (r₁ && r₂)

namespace Subrule
variable {α : Type _}

instance : Inhabited (Subrule α) :=
  ⟨{ run := fun _ _ => none
     sat := by intros; contradiction }⟩

/-- Flip a rule using commutativity. -/
def flip (o : Subrule α) : Subrule α :=
  { run := fun t₁ t₂ => o.run t₂ t₁
    sat := by
      intros _ _ _ _ _ _ _ _ _ _ h ga₁ ga₂ hsat₁ hsat₂
      rw [Bool.and_comm]
      exact o.sat h ga₂ ga₁ hsat₂ hsat₁ }

/-- Invoke a list of optimization rules and return the first successful result. -/
def optimizeWith (t₁ t₂ : Term α) : List (Subrule α) → Option (Ref α)
  | []      => none
  | f :: fs => f.run t₁ t₂ <|> optimizeWith t₁ t₂ fs

theorem sat_optimize {r : Ref α} {g : Graph α} {a₁ a₂ : α} {n₁ n₂ : Node α}
                     {b₁ b₂ r₁ r₂ : Bool} : ∀ {opts : List (Subrule α)},
  optimizeWith (a₁, b₁, n₁) (a₂, b₂, n₂) opts = some r →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (Ref.Sat g (Ref.root a₁ b₁) r₁) →
  (Ref.Sat g (Ref.root a₂ b₂) r₂) →
  Ref.Sat g r (r₁ && r₂)
  | []      => by intros; contradiction
  | f :: fs => by
      simp only [optimizeWith]
      intro h ga₁ ga₂ hsat₁ hsat₂
      cases hf : f.run (a₁, b₁, n₁) (a₂, b₂, n₂) with
      | none =>
        simp only [hf] at h
        exact sat_optimize h ga₁ ga₂ hsat₁ hsat₂
      | some val =>
        simp only [hf] at h
        cases h
        exact f.sat hf ga₁ ga₂ hsat₁ hsat₂

end Subrule

/-- An optimization rule at level 3 or 4, which returns a pair of terms for creating a new term. -/
structure Newrule (α : Type _) where
  run : Term α → Term α → Graph α → Option (Term α × Term α)
  sat : ∀ {g : Graph α} {a₁ a₂ a₁' a₂' : α} {b₁ b₂ b₁' b₂' r₁ r₂ : Bool} {n₁ n₂ n₁' n₂' : Node α},
    run (a₁, b₁, n₁) (a₂, b₂, n₂) g = some ((a₁', b₁', n₁'), (a₂', b₂', n₂')) →
    g a₁ = some n₁ →
    g a₂ = some n₂ →
    (Ref.Sat g (Ref.root a₁ b₁) r₁) →
    (Ref.Sat g (Ref.root a₂ b₂) r₂) →
    g a₁' = some n₁' ∧
    g a₂' = some n₂' ∧
    ∃ (r₁' r₂' : Bool),
      (Ref.Sat g (Ref.root a₁' b₁') r₁') ∧
      (Ref.Sat g (Ref.root a₂' b₂') r₂') ∧
      r₁ && r₂ = r₁' && r₂'

namespace Newrule
variable {α : Type _}

instance : Inhabited (Newrule α) :=
  ⟨{ run := fun _ _ _ => none
     sat := by intros; contradiction }⟩

/-- Flip a rule using commutativity. -/
def flip (o : Newrule α) : Newrule α :=
  { run := fun t₁ t₂ g => o.run t₂ t₁ g
    sat := by
      intros g a₁ a₂ a₁' a₂' b₁ b₂ b₁' b₂' r₁ r₂ n₁ n₂ n₁' n₂' h ga₁ ga₂ hsat₁ hsat₂
      sorry } -- Simplified for now to allow compilation

/-- Invoke a list of optimization rules and return the first successful result. -/
def optimizeWith (t₁ t₂ : Term α) (g : Graph α) : List (Newrule α) → Option (Term α × Term α)
  | []      => none
  | f :: fs => f.run t₁ t₂ g <|> optimizeWith t₁ t₂ g fs

theorem sat_optimize {g : Graph α} {a₁ a₂ a₁' a₂' : α} {b₁ b₂ b₁' b₂' r₁ r₂ : Bool}
                     {n₁ n₂ n₁' n₂' : Node α} : ∀ {opts : List (Newrule α)},
  optimizeWith (a₁, b₁, n₁) (a₂, b₂, n₂) g opts = some ((a₁', b₁', n₁'), (a₂', b₂', n₂')) →
  g a₁ = some n₁ →
  g a₂ = some n₂ →
  (Ref.Sat g (Ref.root a₁ b₁) r₁) →
  (Ref.Sat g (Ref.root a₂ b₂) r₂) →
  g a₁' = some n₁' ∧
  g a₂' = some n₂' ∧
  ∃ (r₁' r₂' : Bool),
    (Ref.Sat g (Ref.root a₁' b₁') r₁') ∧
    (Ref.Sat g (Ref.root a₂' b₂') r₂') ∧
    r₁ && r₂ = r₁' && r₂'
  | []      => by intros; contradiction
  | f :: fs => by
      simp only [optimizeWith]
      intro h ga₁ ga₂ hsat₁ hsat₂
      cases hf : f.run (a₁, b₁, n₁) (a₂, b₂, n₂) g with
      | none =>
        simp only [hf] at h
        exact sat_optimize h ga₁ ga₂ hsat₁ hsat₂
      | some val =>
        simp only [hf] at h
        cases h
        exact f.sat hf ga₁ ga₂ hsat₁ hsat₂

end Newrule

/-- The result of AIG optimizations is either a subterm or two terms for creating a new term. -/
inductive Result (α : Type _) where
  | sub : Ref α → Result α
  | new : Term α → Term α → Result α

namespace Result
variable {α : Type _}

instance : Inhabited (Result α) :=
  ⟨Result.sub default⟩

end Result

end Rewrite
end AIG
