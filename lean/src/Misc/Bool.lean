/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

theorem bool_iff_true {b : Bool} : b ↔ b = true := by
  rfl

/-- Boolean implication. -/
@[inline] def bimplies : Bool → Bool → Bool
  | false, _ => true
  | true, b => b

@[simp]
theorem bimplies_tt {b : Bool} :
    bimplies b true = true := by
  cases b <;> rfl

theorem bimplies_eq_bnot_bor (b₁ b₂ : Bool) :
    bimplies b₁ b₂ = !b₁ || b₂ := by
  cases b₁ <;> cases b₂ <;> rfl

theorem bimplies_modus_ponens {b₁ b₂ : Bool} :
    bimplies b₁ b₂ → b₁ → b₂ := by
  cases b₁ <;> cases b₂ <;> simp [bimplies]

/-- Boolean biconditional. -/
@[inline] def biff : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

@[simp]
theorem biff_tt (b : Bool) : biff b true = b := by
  cases b <;> rfl

@[simp]
theorem biff_ff (b : Bool) : biff b false = !b := by
  cases b <;> rfl

@[simp]
theorem tt_biff (b : Bool) : biff true b = b := by
  cases b <;> rfl

@[simp]
theorem ff_biff (b : Bool) : biff false b = !b := by
  cases b <;> rfl

@[simp]
theorem biff_self (b : Bool) : biff b b = true := by
  cases b <;> rfl

@[simp]
theorem biff_eq_tt_iff_eq (b₁ b₂ : Bool) : biff b₁ b₂ = true ↔ b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp [biff]

theorem biff_eq_bimplies_band_bimplies (b₁ b₂ : Bool) :
    biff b₁ b₂ = bimplies b₁ b₂ && bimplies b₂ b₁ := by
  cases b₁ <;> cases b₂ <;> rfl

theorem biff_eq_bnot_bxor (b₁ b₂ : Bool) :
    biff b₁ b₂ = !(b₁ ^^ b₂) := by
  cases b₁ <;> cases b₂ <;> rfl

theorem bxor_eq_bnot_biff (b₁ b₂ : Bool) :
    (b₁ ^^ b₂) = !biff b₁ b₂ := by
  cases b₁ <;> cases b₂ <;> rfl

@[simp]
theorem biff_coe_iff (b₁ b₂ : Bool) : biff b₁ b₂ ↔ (b₁ ↔ b₂) := by
  cases b₁ <;> cases b₂ <;> simp [biff]

@[simp]
theorem bxor_invol (b₁ b₂ : Bool) : (b₁ ^^ (b₁ ^^ b₂)) = b₂ := by
  cases b₁ <;> simp

theorem cond_eq_or_ands (b₁ b₂ b₃ : Bool) :
    cond b₁ b₂ b₃ = (b₁ && b₂) || (!b₁ && b₃) := by
  cases b₁ <;> simp

namespace Bool

def full_add (a b cin : Bool) : (Bool × Bool) :=
  ((a ^^ b) ^^ cin, (a && b) || (cin && (a ^^ b)))

end Bool
