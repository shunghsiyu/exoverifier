/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.Counter
import Exoverifier.Data.Hashable
import Exoverifier.Misc.Bool

/-!
# And-inverter graphs

This file provides support for and-inverter graphs (AIGs).

An AIG is a directed acyclic graph. Each node takes either zero (variable) or two inputs (AND).
Each edge may be inverted, enabling compact representation of logical operators.

## Implementation notes

* The representation is split into two parts: (unnamed) `Ref` represents top-level inversion or
  constants, while (named) `Node` represents internal nodes. In other words, it maintains that
  there are no constants as internal nodes.

## References

* Robert Brummayer. *C32SAT: A Satisfiable Checker for C Expressions*.
  <http://fmv.jku.at/papers/Brummayer-MasterThesis06.pdf>
-/

namespace AIG

/-- An AIG node is either a variable or a logical conjunction. -/
inductive Node (α : Type _) where
  | var (b : Bool)
  | and (n₁ : α) (b₁ : Bool) (n₂ : α) (b₂ : Bool)
  deriving DecidableEq, Repr

/-- An AIG graph is a partial function from node identifiers to nodes. -/
@[reducible]
def Graph (α : Type _) : Type _ :=
  α → Option (Node α)

namespace Node
variable {α : Type _}

instance : Inhabited (Node α) :=
  ⟨Node.var false⟩

/-- Relate a node in an AIG to a bool it interprets to. -/
inductive Sat (g : Graph α) : α → Bool → Prop where
  | var {b : Bool} {id : α} :
      g id = some (Node.var b) →
      Sat g id b
  | and {b₁ b₂ r₁ r₂ : Bool} {id n₁ n₂ : α} :
      g id = some (Node.and n₁ b₁ n₂ b₂) →
      Sat g n₁ r₁ →
      Sat g n₂ r₂ →
      Sat g id ((xor b₁ r₁) && (xor b₂ r₂))

/-- Two sat derivations of the same AIG and node always agree on the interpretation. -/
theorem sat_inj {g : Graph α} {x : α} {b₁ b₂ : Bool} :
    Sat g x b₁ → Sat g x b₂ → b₁ = b₂ := by
  intro h₁ h₂
  induction h₁ generalizing b₂ with
  | var lookup₁ =>
    cases h₂ with
    | var lookup₂ =>
      rw [lookup₁] at lookup₂
      cases lookup₂
      rfl
    | and lookup₂ _ _ =>
      rw [lookup₁] at lookup₂
      cases lookup₂
  | and lookup₁ sat₁₁ sat₁₂ ih₁ ih₂ =>
    cases h₂ with
    | var lookup₂ =>
      rw [lookup₁] at lookup₂
      cases lookup₂
    | and lookup₂ sat₂₁ sat₂₂ =>
      rw [lookup₁] at lookup₂
      cases lookup₂
      congr 1
      · congr 1
        exact ih₁ sat₂₁
      · congr 1
        exact ih₂ sat₂₂

/-- sat is preserved in bigger graphs. -/
theorem sat_of_subset {g g' : Graph α} {x : α} {b : Bool} :
    Sat g x b → (∀ i n, g i = some n → g' i = some n) → Sat g' x b := by
  intro h l
  induction h with
  | var lookup => exact Sat.var (l _ _ lookup)
  | and lookup _ _ ih₁ ih₂ => exact Sat.and (l _ _ lookup) ih₁ ih₂

end Node

/-- A reference of an AIG node, modeling the top-level edge.

Internal edges are modeled by AND gates in `Node`.
-/
inductive Ref (α : Type _) where
  | top
  | bot
  | root (a : α) (b : Bool)
  deriving DecidableEq, Repr

namespace Ref
variable {α : Type _}

instance : Inhabited (Ref α) :=
  ⟨Ref.top⟩

/-- Make a reference to a node with a regular edge. -/
@[reducible]
def mkReg (a : α) : Ref α :=
  Ref.root a false

/-- Make a reference to a node with an inverted edge. -/
@[reducible]
def mkInv (a : α) : Ref α :=
  Ref.root a true

/-- Evaluate a `Ref` to bool. -/
inductive Sat (g : Graph α) : Ref α → Bool → Prop where
  | top  : Sat g Ref.top true
  | bot  : Sat g Ref.bot false
  | root {a : α} {b r : Bool} :
      Node.Sat g a r →
      Sat g (Ref.root a b) (xor b r)

theorem sat_top_iff {g : Graph α} {b : Bool} :
    Sat g Ref.top b ↔ b = true := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; constructor

theorem sat_bot_iff {g : Graph α} {b : Bool} :
    Sat g Ref.bot b ↔ b = false := by
  constructor
  · intro h; cases h; rfl
  · intro h; cases h; constructor

theorem sat_root_iff {g : Graph α} {a : α} {b r : Bool} :
    Sat g (Ref.root a b) r ↔ Node.Sat g a (xor b r) := by
  constructor
  · intro h
    cases h with
    | root hsat =>
      -- hsat : Node.Sat g a r', where r = xor b r'
      -- We need to show: Node.Sat g a (xor b r)
      -- Since r = xor b r', we have xor b r = xor b (xor b r') = r'
      have xor_invol : ∀ b x, xor b (xor b x) = x := by
        intro b' x; cases b' <;> cases x <;> rfl
      rw [xor_invol]
      exact hsat
  · intro h
    have : r = xor b (xor b r) := by cases b <;> cases r <;> rfl
    rw [this]
    exact Sat.root h

theorem sat_inj {g : Graph α} {x : Ref α} {b₁ b₂ : Bool} :
    Sat g x b₁ → Sat g x b₂ → b₁ = b₂ := by
  intro h₁ h₂
  cases h₁ with
  | top => cases h₂; rfl
  | bot => cases h₂; rfl
  | root hsat₁ =>
    cases h₂ with
    | root hsat₂ =>
      -- hsat₁ : Node.Sat g a r, where b₁ = xor b r
      -- hsat₂ : Node.Sat g a r', where b₂ = xor b r'
      -- Node.sat_inj gives us r = r', so b₁ = b₂
      have eq := Node.sat_inj hsat₁ hsat₂
      rw [eq]

theorem sat_of_subset {g g' : Graph α} {x : Ref α} {b : Bool} :
    Sat g x b → (∀ i n, g i = some n → g' i = some n) → Sat g' x b := by
  intro h l
  cases h with
  | top => constructor
  | bot => constructor
  | root hsat => exact Sat.root (Node.sat_of_subset hsat l)

/-- Invert a `Ref`. -/
@[simp]
protected def neg : Ref α → Ref α
  | Ref.top        => Ref.bot
  | Ref.bot        => Ref.top
  | Ref.root a b   => Ref.root a (!b)

instance : Neg (Ref α) :=
  ⟨Ref.neg⟩

theorem sat_neg_iff {g : Graph α} {r : Ref α} {b : Bool} :
    Sat g (-r) b ↔ Sat g r (!b) := by
  cases r with
  | top =>
    simp only [Neg.neg, Ref.neg]
    rw [sat_top_iff, sat_bot_iff]
    cases b <;> simp
  | bot =>
    simp only [Neg.neg, Ref.neg]
    rw [sat_top_iff, sat_bot_iff]
    cases b <;> simp
  | root a b' =>
    simp only [Neg.neg, Ref.neg, sat_root_iff]
    have : xor (!b') b = xor b' (!b) := by
      cases b' <;> cases b <;> rfl
    rw [this]

theorem neg_invol (x : Ref α) : -(-x) = x := by
  cases x <;> simp [Neg.neg, Ref.neg]

end Ref

end AIG
