/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesXNY2.PartI_Forms.Forms

/-!
# Part I, Chapter 3 — The form class group and Dirichlet composition

Cox, *Primes of the Form x² + ny²*, §3.

Proper equivalence classes of primitive positive definite forms of a fixed
discriminant `D < 0` form a finite abelian group `C(D)` under Dirichlet
composition.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.Forms

/-- Forms of a fixed discriminant `D`, as a subtype of `BinaryQF`. -/
def DiscrForms (D : ℤ) : Type := {f : BinaryQF // f.discr = D}

/-- Proper equivalence as a `Setoid` on the forms of discriminant `D`. (Cox, §3.) -/
def properSetoid (D : ℤ) : Setoid (DiscrForms D) where
  r f g := ProperlyEquivalent f.1 g.1
  iseqv := sorry

/-- The **form class group** `C(D)` as a type: proper equivalence classes of forms
of discriminant `D`. The group law is Dirichlet composition. (Cox, §3.) -/
def FormClassGroup (D : ℤ) : Type := Quotient (properSetoid D)

/-- **Dirichlet composition** of two classes of forms of discriminant `D`.
(Cox, §3, Thm 3.9.) -/
def compose (D : ℤ) : FormClassGroup D → FormClassGroup D → FormClassGroup D := sorry

/-- The class of the **principal form** of discriminant `D` (the identity of
`C(D)`). (Cox, §3.) -/
def principalClass (D : ℤ) : FormClassGroup D := sorry

/-- **The form class group is a finite abelian group** under Dirichlet
composition, with identity the principal class. (Cox, Thm 3.9.) Stated as the
existence of a `CommGroup` structure on the carrier. -/
theorem isCommGroup (D : ℤ) : Nonempty (CommGroup (FormClassGroup D)) := sorry

/-- The form class group of a negative discriminant is finite. (Cox, §3.) -/
theorem finite (D : ℤ) (hD : D < 0) : Nonempty (Fintype (FormClassGroup D)) := sorry

end PrimesXNY2.Forms
