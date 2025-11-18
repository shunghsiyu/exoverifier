/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

/-!
# Abstract domains - STUB

This is a minimal stub for abstract domain infrastructure.
Full implementation to be completed later.
-/

-- Stub type classes - will be replaced with proper definitions
class HasGamma (β : Type _) (α : Type _) where
  γ : α → (β → Prop)

open HasGamma

class AbstrTop (β : Type _) (α : Type _) [HasGamma β α]

class AbstrBot (β : Type _) (α : Type _) [HasGamma β α]

class AbstrJoin (β : Type _) (α₁ α₂ : Type _) [HasGamma β α₁] [HasGamma β α₂]

class AbstrMeet (β : Type _) (α₁ α₂ : Type _) [HasGamma β α₁] [HasGamma β α₂]

-- Stub structures
structure AbstrUnaryTest {β : Type _} (p : β → Prop) (α : Type _) where
  test : α → Bool

structure AbstrBinaryTest {β₁ β₂ : Type _} (p : β₁ → β₂ → Prop) (α₁ α₂ : Type _) where
  test : α₁ → α₂ → Bool

structure AbstrNullaryRelation {β : Type _} (R : β → Prop) (α : Type _) where
  op : α

structure AbstrUnaryRelation {β₁ β₂ : Type _} (R : β₁ → β₂ → Prop) (α₁ α₂ : Type _) where
  op : α₁ → α₂

def AbstrUnaryTransfer {β₁ β₂ : Type _} (f : β₁ → β₂) (α₁ α₂ : Type _) :=
  AbstrUnaryRelation (fun (x : β₁) (y : β₂) => y = f x) α₁ α₂

structure AbstrBinaryRelation {β₁ β₂ β₃ : Type _} (R : β₁ → β₂ → β₃ → Prop)
    (α₁ α₂ α₃ : Type _) where
  op : α₁ → α₂ → α₃

def AbstrBinaryTransfer {β₁ β₂ β₃ : Type _} (f : β₁ → β₂ → β₃) (α₁ α₂ α₃ : Type _) :=
  AbstrBinaryRelation (fun (x : β₁) (y : β₂) (z : β₃) => z = f x y) α₁ α₂ α₃

structure AbstrUnaryInversion {β : Type _} (p : β → Prop) (α₁ α₂ : Type _) where
  inv : α₁ → α₂

structure AbstrBinaryInversion {β₁ β₂ : Type _} (p : β₁ → β₂ → Prop)
    (α₁ α₂ α₁' α₂' : Type _) where
  inv : α₁ → α₂ → (α₁' × α₂')
