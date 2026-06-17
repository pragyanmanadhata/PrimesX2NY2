/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib

/-!
# Part I, Chapter 1 — Fermat, Euler, and descent

Cox, *Primes of the Form x² + ny²*, §1–2.

The first representation theorems: which primes `p` are of the form `x² + y²`,
`x² + 2y²`, `x² + 3y²`, proved by Fermat's method of descent.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.Fermat

/-- **Fermat's two-square theorem** (Cox, Thm 1.2). An odd prime `p` is a sum of
two squares iff `p ≡ 1 (mod 4)`. -/
theorem prime_sq_add_sq (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2) ↔ p % 4 = 1 := by
  sorry

/-- Primes represented by `x² + 2y²` (Cox, §2). For an odd prime `p`, solvable
iff `p ≡ 1, 3 (mod 8)`. -/
theorem prime_sq_add_two_sq (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 2 * y ^ 2) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  sorry

/-- Primes represented by `x² + 3y²` (Cox, §2). For a prime `p > 3`, solvable iff
`p ≡ 1 (mod 3)`. -/
theorem prime_sq_add_three_sq (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 3 * y ^ 2) ↔ p % 3 = 1 := by
  sorry

/-- **Descent step** (Euler, Cox §1–2). If a prime `p` divides a primitively
represented value `x² + n y²`, then `p` is itself represented by the principal
form `x² + n y²`. This is the inductive heart of Fermat's descent. -/
theorem descent_step (n : ℕ) (p : ℕ) (hp : p.Prime) (x y : ℤ)
    (hcop : IsCoprime x y) (hdvd : (p : ℤ) ∣ x ^ 2 + n * y ^ 2) :
    ∃ a b : ℤ, (p : ℤ) = a ^ 2 + n * b ^ 2 := by
  sorry

end PrimesXNY2.Fermat
