/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.BV.Basic
import Exoverifier.Misc.Bool

namespace BV

variable {n : Nat}

/-- Check if all bits satisfy a predicate (identity in this case). -/
protected def all (v : Fin n → Bool) : Bool :=
  (List.ofFn v).all id

/-- Check if any bit satisfies a predicate (identity in this case). -/
protected def any (v : Fin n → Bool) : Bool :=
  (List.ofFn v).any id

theorem all_iff (v : Fin n → Bool) :
  BV.all v ↔ ∀ i, v i := by
  sorry -- Will complete proof later

theorem all_biff_eq_toBool_eq {n : Nat} (b₁ b₂ : Fin n → Bool) :
  (BV.all (fun i => biff (b₁ i) (b₂ i))) = (b₁ = b₂) := by
  sorry -- Will complete proof later

theorem any_eq_toBool_nonzero {n : Nat} (b₁ : Fin n → Bool) :
  BV.any b₁ = (b₁ ≠ 0) := by
  sorry -- Will complete proof later

end BV
