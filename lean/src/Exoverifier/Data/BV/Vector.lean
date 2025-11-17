/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.BV.Basic
import Exoverifier.Misc.Vector

/--
A vector of bits where the MSB is at index 0.
Can be used interchangably with `LsbVector` and `Vector Bool`,
it exists only to document intent.
-/
abbrev MsbVector (n : Nat) : Type := Vector Bool n

/--
A vector of bits where the LSB is at index 0.
Can be used interchangably with `MsbVector` and `Vector Bool`,
it exists only to document intent.
-/
abbrev LsbVector (n : Nat) : Type := Vector Bool n
