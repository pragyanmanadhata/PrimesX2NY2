/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesX2NY2.PartI_Forms.FormClassGroup
import PrimesX2NY2.PartI_Forms.Genus
import PrimesX2NY2.PartII_ClassFieldTheory.Orders

/-!
# Part II, Chapter 6 - The bridge: forms ≅ ideals

Cox, *Primes of the Form x² + ny²*, **Theorem 7.7**.

For a negative discriminant `D = f² d_K`, the form class group `C(D)` is
isomorphic to the ideal class group
of the order `𝒪` of discriminant `D`, intertwining Dirichlet composition with
ideal multiplication.

The order construction and equivalence proofs are unfinished. The signatures
below use provisional ideal-class carriers from `Orders.lean`.
-/

namespace PrimesX2NY2.Bridge

open PrimesX2NY2.Forms PrimesX2NY2.Order

/-- Placeholder for the order obtained by extracting the conductor and field
discriminant from a negative discriminant `D`. The signature does not yet impose
these conditions on `D`. (Cox, §7.) -/
def orderOfDiscr (D : ℤ) : QuadOrder := sorry

/-- The underlying equivalence in Cox's Theorem 7.7, which identifies form
classes with ideal classes of the order. This provisional statement uses an
equivalence of types; it does not yet express a group isomorphism. -/
theorem formClassGroup_equiv_idealClassGroup (O : QuadOrder) :
    Nonempty (FormClassGroup O.discr ≃ O.idealClassGroup) := sorry

/-- A provisional compatibility statement for Cox's Theorem 7.7: an equivalence
`e` carries Dirichlet composition to an operation `mul` on ideal classes. The
operation still needs to be identified with multiplication of ideals. -/
theorem bridge_respects_composition (O : QuadOrder) :
    ∃ (e : FormClassGroup O.discr ≃ O.idealClassGroup)
      (mul : O.idealClassGroup → O.idealClassGroup → O.idealClassGroup),
      ∀ x y, e (compose O.discr x y) = mul (e x) (e y) := sorry

end PrimesX2NY2.Bridge
