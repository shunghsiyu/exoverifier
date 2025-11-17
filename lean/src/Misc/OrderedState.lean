/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Mathlib.Order.Lattice

structure OrderedState (γ : Type*) [Preorder γ] (α : Type*) where
  run : ∀ (s : γ), α × { s' : γ // s ≤ s' }

namespace OrderedState

variable {γ : Type*} [Preorder γ] {α β : Type*}

def pure (x : α) : OrderedState γ α :=
  OrderedState.mk fun s => (x, ⟨s, le_refl s⟩)

def bind (x : OrderedState γ α) (f : α → OrderedState γ β) : OrderedState γ β :=
  OrderedState.mk fun s =>
    let (y, ⟨s', h1⟩) := x.run s
    let (z, ⟨s'', h2⟩) := (f y).run s'
    (z, ⟨s'', le_trans h1 h2⟩)

instance : Pure (OrderedState γ) where
  pure := @pure _ _

instance : Bind (OrderedState γ) where
  bind := @bind _ _

def get : OrderedState γ γ :=
  OrderedState.mk fun s => (s, ⟨s, le_refl s⟩)

def modify (f : γ → γ) (h : ∀ (s : γ), s ≤ f s) : OrderedState γ Unit :=
  OrderedState.mk fun s => ((), ⟨f s, h s⟩)

end OrderedState
