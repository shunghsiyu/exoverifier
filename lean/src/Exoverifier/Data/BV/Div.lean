/-
Copyright (c) 2021 The UNSAT Group. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Xi Wang
-/
import Exoverifier.Data.BV.Basic

/-!
# Division by constant

This file provides support for division by constant.

## References

* Torbjörn Granlund and Peter L. Montgomery. *Division by Invariant Integers using Multiplication*.
  <https://gmplib.org/~tege/divcnst-pldi94.pdf>
-/

namespace BV

-- Theorem 4.2: m / 2^(n + l) can be viewed as an approximation of 1 / y.
theorem div_eq_reciprocal_mul_div_of_reciprocal {n l x y m : Nat} :
  x < 2^n →
  2^(n + l) ≤ m * y →
  m * y ≤ 2^(n + l) + 2^l →
  x / y = m * x / 2^(n + l) := by
  sorry -- Will complete proof later

-- Figure 4.1, without considering overflows (thus not using two shifts).
theorem div_eq_reciprocal_mul_div {n l x y : Nat} :
  let m' := 2^n * (2^l - y) / y + 1
  let t₁ := m' * x / 2^n
  x < 2^n →
  1 < y →
  y < 2^n →
  y ≤ 2^l →
  2^l < 2 * y →
  x / y = (t₁ + x) / 2^l := by
  sorry -- Will complete proof later

end BV
