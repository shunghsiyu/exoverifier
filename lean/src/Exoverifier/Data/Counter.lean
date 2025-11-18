/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

/-!
# Counter - STUB
Stub for counter typeclass (sequential ID allocation).
Full implementation to be completed later.
-/

class Counter (α : Type _) where
  toNat : α → Nat
  init : α
  next : α → α
