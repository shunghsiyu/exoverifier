/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Data.Domain.Basic

/-!
# Trit domain

The trit domain uses three-valued logic: true, false, and unknown.
-/

namespace Domain

-- Placeholder for trit domain implementation

inductive Trit
  | ff : Trit
  | tt : Trit
  | unknown : Trit
deriving DecidableEq, Repr

-- Instance declarations and operations to be added

end Domain
