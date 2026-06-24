/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.FormClassGroup
import PrimesX2NY2.PartII_ClassFieldTheory.Orders

/-!
# Part II, Chapter 6 - The bridge: forms ≅ ideals

Cox, *Primes of the Form x² + ny²*, **Theorem 7.7**.

The central structural result of Part II: for a negative discriminant
`D = f² d_K`, the form class group `C(D)` is isomorphic to the ideal class group
of the order `𝒪` of discriminant `D`, intertwining Dirichlet composition with
ideal multiplication.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesX2NY2.Bridge

open PrimesX2NY2.Forms PrimesX2NY2.Order

/-- The order whose discriminant equals a given negative discriminant `D`
(conductor and field discriminant extracted from `D`). Placeholder. (Cox, §7.) -/
def orderOfDiscr (D : ℤ) : QuadOrder := sorry

/-- **The bridge (Cox, Theorem 7.7).** For the order `𝒪` of discriminant `D < 0`,
the form class group `C(D)` is isomorphic, as a group, to the ideal class group
`C(𝒪)`. Stated as a multiplicative equivalence built from a bijection. -/
theorem formClassGroup_equiv_idealClassGroup (O : QuadOrder) :
    Nonempty (FormClassGroup O.discr ≃ O.idealClassGroup) := sorry

/-- The bridge intertwines Dirichlet composition on forms with ideal
multiplication on ideal classes: there is an equivalence `e` and an ideal-class
multiplication `mul` with `e (f ∘ g) = mul (e f) (e g)`. (Cox, Thm 7.7.) -/
theorem bridge_respects_composition (O : QuadOrder) :
    ∃ (e : FormClassGroup O.discr ≃ O.idealClassGroup)
      (mul : O.idealClassGroup → O.idealClassGroup → O.idealClassGroup),
      ∀ x y, e (compose O.discr x y) = mul (e x) (e y) := sorry

end PrimesX2NY2.Bridge
