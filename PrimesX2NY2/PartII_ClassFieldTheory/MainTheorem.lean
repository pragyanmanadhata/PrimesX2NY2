/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.FormClassGroup
import PrimesX2NY2.PartII_ClassFieldTheory.Orders
import PrimesX2NY2.PartII_ClassFieldTheory.RingClassField

/-!
# Part II, Chapter 8 - The Main Theorem

Cox, *Primes of the Form x² + ny²*, **Theorem 9.2** (and Cor 9.4).

The synthesis of Part I and II: for suitable `n`, a prime `p ∤ n` is of the form
`x² + ny²` iff it splits completely in the ring class field, iff a class
polynomial `f_n` has a root mod `p` together with the residue condition
`(−n / p) = 1`.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.MainTheorem

open PrimesX2NY2.Order PrimesX2NY2.RingClassField

/-- The **class polynomial** `f_n(x) ∈ ℤ[x]` whose roots generate the ring class
field of the order `ℤ[√(−n)]`; its existence and integrality are part of the main
theorem. (Cox, Thm 9.2.) Placeholder. -/
def classPolynomial (n : ℕ) : Polynomial ℤ := sorry

/-- The class polynomial is monic. (Cox, Thm 9.2.) -/
theorem classPolynomial_monic (n : ℕ) : (classPolynomial n).Monic := sorry

/-- The degree of the class polynomial is the class number `h(−4n)`. (Cox, §9.) -/
theorem classPolynomial_natDegree (n : ℕ) :
    (classPolynomial n).natDegree =
      Nat.card (PrimesX2NY2.Forms.FormClassGroup (-4 * n)) := sorry

/-- **Main Theorem - splitting form** (Cox, Thm 9.2). For the order `𝒪` of
discriminant `−4n`, an odd prime `p` not dividing `n` (nor the conductor) is
represented as `p = x² + n y²` iff `p` splits completely in the ring class
field. -/
theorem prime_repr_iff_splits (n : ℕ) (O : QuadOrder) (p : ℕ) (hp : p.Prime)
    (hpn : ¬ (p : ℤ) ∣ n) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + n * y ^ 2) ↔ SplitsCompletely O p := by
  sorry

/-- **Main Theorem - class polynomial form** (Cox, Cor 9.4). Representability is
detected by a root of the class polynomial mod `p` together with the quadratic
residue condition `(−n / p) = 1`. This is the computational criterion. -/
theorem prime_repr_iff_classPoly_root (n : ℕ) (p : ℕ) (hp : p.Prime) :
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + n * y ^ 2) ↔
      IsSquare ((-(n : ℤ)) : ZMod p) ∧
        ∃ r : ZMod p,
          (classPolynomial n).eval₂ (Int.castRingHom (ZMod p)) r = 0 := by
  sorry

end PrimesX2NY2.MainTheorem
