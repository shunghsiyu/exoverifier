/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.SAT.Basic

/-!
# CNF (Conjunctive Normal Form)

This file provides basic support for formulas in conjunctive normal form (CNF).

## Implementation notes

Simplified List-based implementation for initial migration.
A literal consists of a variable and its sign (true for ¬x, false for x).

## References

* <https://en.wikipedia.org/wiki/Conjunctive_normal_form>
-/

namespace Sat
namespace CNF

/-- A literal consists of a variable and its sign (`true` for ¬x, `false` for x). -/
structure Literal (α : Type _) where
  var : α
  sign : Bool

namespace Literal
variable {α : Type _}

/-- Create a positive literal. -/
def mkPos (a : α) : Literal α := ⟨a, false⟩

/-- Create a negative literal. -/
def mkNeg (a : α) : Literal α := ⟨a, true⟩

instance : HasSat α (Literal α) where
  sat p l := (xor (p l.var) l.sign) = true

instance : Neg (Literal α) where
  neg l := ⟨l.var, !l.sign⟩

@[simp]
theorem neg_neg (l : Literal α) : -(-l) = l := by
  cases l
  simp [Neg.neg]

theorem sat_neg_iff (p : α → Bool) (l : Literal α) :
    HasSat.sat p (-l) ↔ ¬HasSat.sat p l := by
  cases l with | mk a b =>
  simp only [Neg.neg, HasSat.sat, xor]
  cases b <;> cases p a <;> decide

@[simp]
theorem not_sat_neg_iff (p : α → Bool) (l : Literal α) :
    ¬HasSat.sat p (-l) ↔ HasSat.sat p l := by
  rw [sat_neg_iff]
  simp

end Literal

/-- A clause is a disjunction of literals (list-based). -/
@[reducible] def Clause (α : Type _) := List (Literal α)

namespace Clause
variable {α : Type _}

/-- Empty clause -/
def empty : Clause α := []

instance : HasSat α (Clause α) where
  sat p c := c.any fun l => (xor (p l.var) l.sign)

theorem sat_iff_exists (p : α → Bool) (c : Clause α) :
    HasSat.sat p c ↔ ∃ (l : Literal α), l ∈ c ∧ HasSat.sat p l := by
  simp only [HasSat.sat, List.any_eq_true]

theorem unsat_empty : unsatisfiable (empty : Clause α) := by
  intro p
  simp only [HasSat.sat, empty, List.any_nil, Bool.false_eq_true, not_false_eq_true]

end Clause

/-- A CNF formula is a conjunction of clauses (list-based). -/
@[reducible] def Formula (α : Type _) := List (Clause α)

namespace Formula
variable {α : Type _}

/-- Empty formula (trivially satisfiable) -/
def empty : Formula α := []

instance : HasSat α (Formula α) where
  sat p f := f.all fun c => c.any fun l => (xor (p l.var) l.sign)

theorem sat_iff_forall (p : α → Bool) (f : Formula α) :
    HasSat.sat p f ↔ ∀ (c : Clause α), c ∈ f → HasSat.sat p c := by
  simp only [HasSat.sat, List.all_eq_true]

theorem sat_empty (p : α → Bool) : HasSat.sat p (empty : Formula α) := by
  simp only [HasSat.sat, empty, List.all_nil]

end Formula

end CNF
end Sat
