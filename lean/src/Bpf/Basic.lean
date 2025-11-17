/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Data.Bv.Basic
import Data.Bv.Vector
import Mathlib.Data.List.Alist
import Data.Trie.Basic
import Mathlib.Data.Vector.Basic
import Misc.FinEnum
import Misc.Vector

/-!
# BPF Semantics

Core definitions for BPF (Berkeley Packet Filter) programs:
- Registers and instruction types
- Values (scalar, pointer, uninitialized)
- ALU and jump operations
- Memory operations

This forms the foundation for BPF verification.
-/

namespace Bpf

abbrev I64 : Type := Fin 64 → Bool
abbrev I32 : Type := Fin 32 → Bool

/-- An oracle makes the nondeterministic choices during execution of a BPF program. -/
structure Oracle where
  rng : ℕ → I64

namespace Oracle

instance : Inhabited Oracle where
  default := ⟨fun _ => default⟩

end Oracle

/-- Truncate a 64-bit value to the lower 32 bits. -/
@[reducible]
private def trunc32 (i : I64) : I32 :=
  -- Note: Bv.extract needs to be properly defined in Bv/Concat.lean
  sorry -- Placeholder: Bv.extract 31 0 _ _ i

/-- The number of BPF registers. -/
abbrev nregs : ℕ := 12

/-- BPF registers -/
inductive Reg : Type
  | R0 : Reg
  | R1 : Reg
  | R2 : Reg
  | R3 : Reg
  | R4 : Reg
  | R5 : Reg
  | R6 : Reg
  | R7 : Reg
  | R8 : Reg
  | R9 : Reg
  | FP : Reg
  | AX : Reg
deriving DecidableEq, Inhabited, Repr

namespace Reg

/-- Caller-saved registers according to the BPF semantics. -/
def callerSaved : List Reg :=
  [R0, R1, R2, R3, R4, R5]

-- Note: to_vector, fin_enum, to_fin need Vector and FinEnum properly migrated
-- Placeholder for now

end Reg

/-- BPF instruction classes -/
inductive InsnClass : Type
  | alu : InsnClass     -- Arithmetic/logic operations
  | jmp : InsnClass     -- Jump operations
  | ld : InsnClass      -- Load operations
  | ldx : InsnClass     -- Load indexed
  | st : InsnClass      -- Store operations
  | stx : InsnClass     -- Store indexed
deriving DecidableEq, Repr

/-- ALU operations -/
inductive AluOp : Type
  | add : AluOp
  | sub : AluOp
  | mul : AluOp
  | div : AluOp
  | or_ : AluOp
  | and_ : AluOp
  | lsh : AluOp
  | rsh : AluOp
  | neg : AluOp
  | mod : AluOp
  | xor : AluOp
  | mov : AluOp
  | arsh : AluOp
deriving DecidableEq, Repr

/-- Jump operations -/
inductive JmpOp : Type
  | ja : JmpOp    -- Jump always
  | jeq : JmpOp   -- Jump if equal
  | jgt : JmpOp   -- Jump if greater (unsigned)
  | jge : JmpOp   -- Jump if greater or equal (unsigned)
  | jset : JmpOp  -- Jump if bit set
  | jne : JmpOp   -- Jump if not equal
  | jsgt : JmpOp  -- Jump if greater (signed)
  | jsge : JmpOp  -- Jump if greater or equal (signed)
  | call : JmpOp  -- Function call
  | exit : JmpOp  -- Exit
  | jlt : JmpOp   -- Jump if less (unsigned)
  | jle : JmpOp   -- Jump if less or equal (unsigned)
  | jslt : JmpOp  -- Jump if less (signed)
  | jsle : JmpOp  -- Jump if less or equal (signed)
deriving DecidableEq, Repr

/-- BPF values: scalar, pointer, or uninitialized -/
inductive Value : Type
  | scalar : I64 → Value
  | ptr : I64 → Value  -- Pointer with offset
  | uninit : Value
deriving Repr

-- Additional definitions for instructions, semantics, etc. to be added
-- This includes:
-- - Instruction type
-- - Memory model
-- - Execution semantics
-- - Safety conditions

end Bpf
