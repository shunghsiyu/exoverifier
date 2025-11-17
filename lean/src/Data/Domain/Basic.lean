/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Misc.WithBot
import Misc.WithTop
import Mathlib.Order.BoundedOrder
import Mathlib.Data.Fintype.Basic

/-!
# Abstract domains

Basic definitions of domains for abstract interpretation.

## References

* <https://xavierleroy.org/courses/Eugene-2011/Analyzer1.html>
* <https://xavierleroy.org/courses/Eugene-2011/Analyzer2.html>
* <https://hal.archives-ouvertes.fr/tel-01327023/document>
-/

/--
HasGamma β α means that the type α can serve as an abstraction of sets of concrete values of type β.
There are two definitions that must be met:
A function γ which maps an abstract value to its set of concrete values; and
a function `abstract` which maps a single concrete value into an abstract value.

Assume that α uniquely determines β.
-/
class HasGamma (β : outParam Type*) (α : Type*) where
  γ : α → Set β

open HasGamma

/--
HasDecidableGamma means the γ relation is decidable.
-/
class HasDecidableGamma (β : outParam Type*) (α : Type*) [HasGamma β α] where
  dec_γ : ∀ (x : α), DecidablePred (γ x)

/--
AbstrLe β α is an ordering on abstract values that respects set inclusion using γ.
-/
class AbstrLe (β : outParam Type*) (α : Type*) [HasGamma β α] extends LE α where
  dec_le : DecidableRel (· ≤ ·)
  le_correct : ∀ ⦃x y : α⦄, x ≤ y → γ x ⊆ γ y

/--
AbstrTop β α means there exists an element ⊤ that maps to the complete set of β.
-/
class AbstrTop (β : outParam Type*) (α : Type*) [HasGamma β α] extends Top α where
  top_correct : ∀ (c : β), γ (⊤ : α) c

/--
AbstrBot β α means there exists an element ⊥ that maps to the empty set of β.
-/
class AbstrBot (β : outParam Type*) (α : Type*) [HasGamma β α] extends Bot α where
  bot_correct : ∀ (c : β), ¬(γ (⊥ : α) c)

/--
AbstrJoin β α means that there exists a join operation which respects set union using γ.
-/
class AbstrJoin (β : outParam Type*) (α₁ α₂ : Type*) [HasGamma β α₁] [HasGamma β α₂] where
  join : α₁ → α₁ → α₂
  join_correct : ∀ ⦃x y : α₁⦄, γ x ∪ γ y ⊆ γ (join x y)

/--
AbstrMeet β α means that there exists a meet operation which respects set intersection using γ.
-/
class AbstrMeet (β : outParam Type*) (α₁ α₂ : Type*) [HasGamma β α₁] [HasGamma β α₂] where
  meet : α₁ → α₁ → α₂
  meet_correct : ∀ ⦃x y : α₁⦄, γ x ∩ γ y ⊆ γ (meet x y)

/--
A test function for abstract values. Given some test `p` on concrete values,
it determines whether that test is satisfied for all concrete values represented by the
abstract value.
-/
structure AbstrUnaryTest {β : Type*} (p : β → Prop) (α : Type*) [HasGamma β α] where
  test : α → Bool
  test_correct : ∀ {x : α}, test x = true → ∀ c ∈ γ x, p c

/--
A binary test function for abstract values.
-/
structure AbstrBinaryTest {β : Type*} (p : β → β → Prop) (α : Type*) [HasGamma β α] where
  test : α → α → Bool
  test_correct : ∀ {x y : α}, test x y = true → ∀ c₁ ∈ γ x, ∀ c₂ ∈ γ y, p c₁ c₂

/--
A unary operation on abstract values.
-/
class AbstrUnaryOp {β : Type*} (op : β → β) (α₁ α₂ : Type*) [HasGamma β α₁] [HasGamma β α₂] where
  apply : α₁ → α₂
  apply_correct : ∀ {x : α₁}, (op '' γ x) ⊆ γ (apply x)

/--
A binary operation on abstract values.
-/
class AbstrBinaryOp {β : Type*} (op : β → β → β) (α₁ α₂ : Type*)
    [HasGamma β α₁] [HasGamma β α₂] where
  apply : α₁ → α₁ → α₂
  apply_correct : ∀ {x y : α₁}, Set.image2 op (γ x) (γ y) ⊆ γ (apply x y)

-- Additional abstract domain utilities and instances to be added

end
