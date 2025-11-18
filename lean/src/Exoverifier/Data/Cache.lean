/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/

/-!
# Cache - STUB
Stub for node cache infrastructure.
Full implementation to be completed later.
-/

class Cache (α : outParam (Type _)) (β : Type _) where
  insert : α → β → β × Bool

def Cache' : Type := Unit  -- Stub type
