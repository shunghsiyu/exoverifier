/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.BV.Basic
import Exoverifier.Misc.Fin

namespace BV

variable {n n₁ n₂ : Nat}

/-- Concatenate two bitvectors. -/
def concat (v₁ : Fin n₁ → Bool) (v₂ : Fin n₂ → Bool) : Fin (n₁ + n₂) → Bool :=
  fun i =>
    if h : i.val < n₂ then
      v₂ ⟨i.val, h⟩
    else
      v₁ ⟨i.val - n₂, by omega⟩

theorem toNat_concat (v₁ : Fin n₁ → Bool) (v₂ : Fin n₂ → Bool) :
  toNat (concat v₁ v₂) = toNat v₂ + 2^n₂ * toNat v₁ := by
  sorry -- Will complete proof later

section drop_take

/-- Drop the lower i bits. -/
def drop (i : Nat) (v : Fin n → Bool) : Fin (n - i) → Bool :=
  fun ⟨x, h⟩ => v ⟨x + i, by omega⟩

/-- Extract the lower i bits. -/
def take (i : Nat) (v : Fin n → Bool) : Fin (min i n) → Bool :=
  fun ⟨x, h⟩ => v ⟨x, Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)⟩

theorem concat_drop_take (i : Nat) (v : Fin n → Bool) :
  HEq (concat (drop i v) (take i v)) v := by
  sorry -- Will complete proof later

theorem toNat_drop (i : Nat) (v : Fin n → Bool) :
  toNat (drop i v) = toNat v / 2^i := by
  sorry -- Will complete proof later

theorem toNat_take (i : Nat) (v : Fin n → Bool) :
  toNat (take i v) = toNat v % 2^i := by
  sorry -- Will complete proof later

end drop_take

/-! ### Extract and zero-extend operations -/
section extract

/-- Extract bits [high:low]. Result width depends on high and low. -/
def extract (high low : Nat) (v : Fin n → Bool) : Fin (min (high - low + 1) (n - low)) → Bool :=
  take (high - low + 1) (drop low v)

/-- Zero-extend to a larger width. -/
def zeroExtend (m : Nat) (v : Fin n → Bool) : Fin (m + n) → Bool :=
  concat (allFalse (n := m)) v

/-- Sign-extend to a larger width. -/
def signExtend (m : Nat) (v : Fin n → Bool) : Fin (m + n) → Bool :=
  if msb v then
    concat (allTrue (n := m)) v
  else
    concat (allFalse (n := m)) v

end extract

end BV
