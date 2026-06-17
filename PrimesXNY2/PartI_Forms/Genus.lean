/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesXNY2.PartI_Forms.FormClassGroup

/-!
# Part I, Chapter 4 — Genus theory and representation

Cox, *Primes of the Form x² + ny²*, §3 (genus theory).

Genus theory partitions the form class group; the principal genus is the subgroup
of squares, and genus characters decide which primes a form represents.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.Genus

open PrimesXNY2.Forms

/-- A form `f` **represents** an integer `m` if `m = f(x, y)` for some integers
`x, y`. (Cox, §1–2.) -/
def Represents (f : BinaryQF) (m : ℤ) : Prop := ∃ x y : ℤ, f.eval x y = m

/-- A form `f` **properly represents** `m` if `m = f(x, y)` with `gcd(x, y) = 1`.
(Cox, §2.) -/
def ProperlyRepresents (f : BinaryQF) (m : ℤ) : Prop :=
  ∃ x y : ℤ, f.eval x y = m ∧ IsCoprime x y

/-- The **genus** of a form of discriminant `D`: the set of residues in
`(ℤ/Dℤ)` represented by the form, which is constant on a genus. (Cox, §3.) -/
def genus (D : ℤ) (f : BinaryQF) : Set (ZMod D.natAbs) := sorry

/-- The **principal genus**: the genus of the principal form, equivalently the
subgroup of squares in `C(D)`. (Cox, Thm 3.15.) -/
def principalGenus (D : ℤ) : Set (ZMod D.natAbs) := sorry

/-- **Representation criterion via residues** (Cox, Thm 2.16 / §3). A prime `p`
not dividing `D` is properly represented by some form of discriminant `D` iff `D`
is a quadratic residue mod `p`. -/
theorem properlyRepresents_iff_isSquare (D : ℤ) (p : ℕ) (hp : p.Prime)
    (hpD : ¬ (p : ℤ) ∣ D) :
    (∃ f : BinaryQF, f.discr = D ∧ ProperlyRepresents f p) ↔ IsSquare (D : ZMod p) := by
  sorry

/-- **Genus characters determine representation** (Cox, §3). When the genus
number is the full `2`-torsion quotient, congruence conditions on `p` pin down
exactly which form of discriminant `D` represents `p`; in particular for one
class per genus the form `x² + ny²` is detected by congruences alone. -/
theorem represents_principal_iff_congruence (n : ℕ) (p : ℕ) (hp : p.Prime) :
    ProperlyRepresents ⟨1, 0, (n : ℤ)⟩ (p : ℤ) ↔
      (∃ S : Finset (ZMod (4 * n)), (p : ZMod (4 * n)) ∈ S) := by
  sorry

end PrimesXNY2.Genus
