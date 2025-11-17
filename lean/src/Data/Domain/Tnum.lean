/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Data.Domain.Basic
import Data.Bv.Basic

/-!
# Tnum domain

The tnum (tracked number) domain tracks known and unknown bits in bitvectors.
This is used in the Linux kernel BPF verifier.

A tnum consists of two bitvectors:
- `value`: the known bits
- `mask`: bits that are unknown (1 = unknown, 0 = known)
-/

namespace Domain

-- Placeholder for tnum domain implementation
-- This needs detailed migration from Lean 3

structure Tnum (n : ℕ) where
  value : Fin n → Bool
  mask : Fin n → Bool
  -- Invariant: value & mask = 0 (known bits in value must have mask = 0)

-- Instance declarations and operations to be added
-- instance : HasGamma (Fin n → Bool) (Tnum n) := ...
-- instance : AbstrJoin (Fin n → Bool) (Tnum n) := ...
-- etc.

end Domain
