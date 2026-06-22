/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesXNY2.PartI_Forms.Forms

/-!
# Part I, Chapter 3 — The form class group and Dirichlet composition

Cox, *Primes of the Form x² + ny²*, §3.A.

Proper equivalence classes of primitive positive definite forms of a fixed
discriminant `D < 0` form a finite abelian group `C(D)` under Dirichlet
composition.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.Forms

/-- The **opposite** of `f = a x² + b x y + c y²` is `a x² − b x y + c y²`. Its class
is the inverse of the class of `f` in `C(D)`. (Cox §3, Thm 3.9.) -/
def BinaryQF.opposite (f : BinaryQF) : BinaryQF := ⟨f.a, -f.b, f.c⟩

/-- The carrier for the form class group: primitive forms of discriminant `D` with
positive leading coefficient (for `D < 0` this is exactly the primitive positive
definite forms). (Cox §3.) -/
def DiscrForms (D : ℤ) : Type := {f : BinaryQF // f.discr = D ∧ f.Primitive ∧ 0 < f.a}

/-- Proper equivalence as a `Setoid` on the forms of discriminant `D`. (Cox, §3.) -/
def properSetoid (D : ℤ) : Setoid (DiscrForms D) where
  r f g := ProperlyEquivalent f.1 g.1
  iseqv := ⟨fun f => properlyEquivalent_equivalence.refl f.1,
    fun h => properlyEquivalent_equivalence.symm h,
    fun h₁ h₂ => properlyEquivalent_equivalence.trans h₁ h₂⟩

/-- The **form class group** `C(D)` as a type: proper equivalence classes of
primitive positive definite forms of discriminant `D`. The group law is Dirichlet
composition. (Cox, §3.) -/
def FormClassGroup (D : ℤ) : Type := Quotient (properSetoid D)

/-- The class in `C(D)` of a primitive form `f` with positive leading coefficient. -/
def classOf (D : ℤ) (f : BinaryQF) (h : f.discr = D ∧ f.Primitive ∧ 0 < f.a) :
    FormClassGroup D :=
  Quotient.mk (properSetoid D) ⟨f, h⟩

/-- **Lemma 3.2** (Cox §3). For forms `f = a x²+ b x y + c y²` and
`g = a' x²+ b' x y + c' y²` of discriminant `D` with `gcd(a, a', (b+b')/2) = 1`,
there is a `B`, unique modulo `2 a a'`, with `B ≡ b (2a)`, `B ≡ b' (2a')`, and
`B² ≡ D (4 a a')`. -/
theorem lemma_3_2 (a b c a' b' c' D : ℤ)
    (hf : b ^ 2 - 4 * a * c = D) (hg : b' ^ 2 - 4 * a' * c' = D)
    (hcop : Int.gcd (Int.gcd a a') ((b + b') / 2) = 1) :
    ∃ B : ℤ, (B ≡ b [ZMOD (2 * a)]) ∧ (B ≡ b' [ZMOD (2 * a')])
        ∧ (B ^ 2 ≡ D [ZMOD (4 * a * a')])
        ∧ ∀ B' : ℤ, (B' ≡ b [ZMOD (2 * a)]) ∧ (B' ≡ b' [ZMOD (2 * a')])
            ∧ (B' ^ 2 ≡ D [ZMOD (4 * a * a')]) → B' ≡ B [ZMOD (2 * a * a')] := by
  sorry

/-- **Lemma 3.5** (Cox §3). For `p₁,…,pᵣ, q₁,…,qᵣ, m` with `gcd(p₁,…,pᵣ, m) = 1`,
the congruences `pᵢ B ≡ qᵢ (mod m)` have a (unique) solution `B` iff the
compatibility conditions `pᵢ qⱼ ≡ pⱼ qᵢ (mod m)` hold for all `i, j`. -/
theorem lemma_3_5 (r : ℕ) (p q : Fin r → ℤ) (m : ℤ)
    (hcop : ∃ (t : Fin r → ℤ) (s : ℤ), s * m + ∑ i, t i * p i = 1) :
    (∃ B : ℤ, ∀ i, p i * B ≡ q i [ZMOD m]) ↔ (∀ i j, p i * q j ≡ p j * q i [ZMOD m]) := by
  sorry

/-- The **Dirichlet composition** of two forms `f`, `g` of discriminant `D` with
`gcd(a, a', (b+b')/2) = 1`: the form `a a' x² + B x y + ((B²−D)/4 a a') y²`, where
`B` is the integer of Lemma 3.2. (Cox §3, (3.7).) -/
def dirichletForm (f g : BinaryQF) : BinaryQF := sorry

/-- **Proposition 3.8** (Cox §3). The Dirichlet composition `dirichletForm f g` of
two primitive positive definite forms of discriminant `D` (with the coprimality
hypothesis) is again primitive positive definite of discriminant `D`. -/
theorem prop_3_8 (f g : BinaryQF) (D : ℤ) (hf : f.discr = D) (hg : g.discr = D)
    (hfp : f.Primitive) (hgp : g.Primitive) (hfa : 0 < f.a) (hga : 0 < g.a)
    (hcop : Int.gcd (Int.gcd f.a g.a) ((f.b + g.b) / 2) = 1) :
    (dirichletForm f g).discr = D ∧ (dirichletForm f g).Primitive
      ∧ 0 < (dirichletForm f g).a := by
  sorry

/-- **Dirichlet composition** of two classes of forms of discriminant `D`.
(Cox, §3, Thm 3.9.) -/
def compose (D : ℤ) : FormClassGroup D → FormClassGroup D → FormClassGroup D := sorry

/-- The class of the **principal form** of discriminant `D` (the identity of
`C(D)`). (Cox, §3.) -/
def principalClass (D : ℤ) : FormClassGroup D := sorry

/-- **Theorem 3.9** (Cox §3). For `D < 0`, Dirichlet composition makes `C(D)` a
finite abelian group: it is associative and commutative, the principal class is a
right identity, and every class has an inverse. (Faithful replacement of the
earlier vacuous `Nonempty (CommGroup …)`, which holds for any nonempty type.) -/
theorem isCommGroup (D : ℤ) (hD : D < 0) :
    (∀ x y z : FormClassGroup D, compose D (compose D x y) z = compose D x (compose D y z))
      ∧ (∀ x y : FormClassGroup D, compose D x y = compose D y x)
      ∧ (∀ x : FormClassGroup D, compose D x (principalClass D) = x)
      ∧ (∀ x : FormClassGroup D, ∃ y : FormClassGroup D, compose D x y = principalClass D) := by
  sorry

/-- **Theorem 3.9, inverse** (Cox §3). The inverse of the class of `f` is the class
of the opposite form `a x² − b x y + c y²`. -/
theorem thm_3_9_inverse (D : ℤ) (f : BinaryQF) (hd : f.discr = D)
    (hp : f.Primitive) (ha : 0 < f.a)
    (hd' : f.opposite.discr = D) (hp' : f.opposite.Primitive) (ha' : 0 < f.opposite.a) :
    compose D (classOf D f ⟨hd, hp, ha⟩) (classOf D f.opposite ⟨hd', hp', ha'⟩)
      = principalClass D := by
  sorry

/-- The number of distinct odd primes dividing `D`. (Cox §3, Prop 3.11.) -/
def oddPrimeDivisorCount (D : ℤ) : ℕ := (D.natAbs.primeFactors.erase 2).card

/-- The exponent `μ` of Cox, Proposition 3.11: the number of *assigned characters*.
If `D ≡ 1 (mod 4)`, `μ = r`; if `D = −4n`, it is determined by `n (mod 8)` as in
Cox's table, where `r` is the number of odd primes dividing `D`. -/
def mu (D : ℤ) : ℕ :=
  let r := oddPrimeDivisorCount D
  if D % 4 = 1 then r
  else
    let n := (-D) / 4
    if n % 4 = 1 ∨ n % 4 = 2 then r + 1
    else if n % 4 = 3 then r
    else if n % 8 = 0 then r + 2 else r + 1

/-- **Lemma 3.10** (Cox §3). A reduced primitive form `f = a x²+ b x y + c y²` of
discriminant `D` has order `≤ 2` in `C(D)` (its class squares to the principal
class) iff `b = 0`, `a = b`, or `a = c`. -/
theorem lemma_3_10 (D : ℤ) (f : BinaryQF) (hd : f.discr = D) (hp : f.Primitive)
    (ha : 0 < f.a) (hr : f.Reduced) :
    compose D (classOf D f ⟨hd, hp, ha⟩) (classOf D f ⟨hd, hp, ha⟩) = principalClass D
      ↔ (f.b = 0 ∨ f.a = f.b ∨ f.a = f.c) := by
  sorry

/-- **Proposition 3.11** (Cox §3). For `D ≡ 0,1 (mod 4)` negative, the class group
`C(D)` has exactly `2^{μ−1}` elements of order `≤ 2`, where `μ = mu D`. -/
theorem prop_3_11 (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    {x : FormClassGroup D | compose D x x = principalClass D}.ncard = 2 ^ (mu D - 1) := by
  sorry

/-- The form class group of a negative discriminant is finite. (Cox, §3.) -/
theorem finite (D : ℤ) (hD : D < 0) : Nonempty (Fintype (FormClassGroup D)) := sorry

end PrimesXNY2.Forms
