/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Mathlib.Order.BoundedOrder.Basic

/-!
# Ordering instances for Option types

This module provides partial order instances for function types returning Option.
-/

namespace Option

variable {α β : Type _}

/-- Partial order instance for functions returning Option -/
instance : LE (α → Option β) where
  le x y := ∀ {a : α} {b : β}, x a = some b → y a = some b

instance instPreorder : Preorder (α → Option β) where
  le_refl := fun _ => by
    intros a b hab
    exact hab
  le_trans := fun _ _ _ h₁ h₂ => by
    intros a b hab
    exact h₂ (h₁ hab)

instance instPartialOrder : PartialOrder (α → Option β) where
  le_antisymm := fun x y h₁ h₂ => by
    funext a
    cases ha : x a with
    | none =>
      cases ha' : y a with
      | none => rfl
      | some b =>
        have : y a = some b := ha'
        have : x a = some b := h₂ this
        rw [ha] at this
        cases this
    | some b =>
      have : x a = some b := ha
      have : y a = some b := h₁ this
      rw [this]

/-- Bottom element for functions returning Option -/
instance : Bot (α → Option β) where
  bot := fun _ => none

instance instOrderBot : OrderBot (α → Option β) where
  bot_le := fun _ => by
    intros a b hab
    simp [Bot.bot] at hab

end Option

