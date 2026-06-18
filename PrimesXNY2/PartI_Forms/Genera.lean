/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesXNY2.PartI_Forms.Genus

/-!
# Part I, Chapter 3 — Genus theory of Gauss and convenient numbers

Cox, *Primes of the Form x² + ny²*, §3.B–C.

Assigned characters package the genus of a form into a sign vector in `{±1}^μ`.
The number of genera is `2^{μ−1}`, the principal genus is the subgroup of squares
`C(D)²`, and a positive integer `n` is one of Euler's convenient numbers iff every
genus of discriminant `−4n` consists of a single class.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.Genera

open PrimesXNY2.Forms PrimesXNY2.Genus

/-- The character `δ(a) = (−1)^{(a−1)/2}` on odd integers (Cox §3.B): `+1` if
`a ≡ 1 (mod 4)`, `−1` if `a ≡ 3 (mod 4)`. -/
def deltaChar (a : ℤ) : ℤ := if a % 4 = 1 then 1 else -1

/-- The character `ε(a) = (−1)^{(a²−1)/8}` on odd integers (Cox §3.B): `+1` if
`a ≡ ±1 (mod 8)`, `−1` if `a ≡ ±3 (mod 8)`. -/
def epsilonChar (a : ℤ) : ℤ := if a % 8 = 1 ∨ a % 8 = 7 then 1 else -1

/-- The **assigned characters** assembled into the homomorphism
`Ψ : (ℤ/Dℤ)ˣ → {±1}^μ` of Cox (3.16): the components are `χᵢ(·) = (·/pᵢ)` for the
odd primes `pᵢ ∣ D`, together with `δ` and/or `ε` as dictated by `D (mod 8)`. -/
def Psi (D : ℤ) : (ZMod D.natAbs)ˣ → (Fin (mu D) → ℤˣ) := sorry

/-- The **complete character** (genus map) `Φ : C(D) → {±1}^μ` of Cox (3.12),
sending a class to the assigned-character vector of any value coprime to `D` it
represents. Its fibers are the genera. -/
def genusVector (D : ℤ) : FormClassGroup D → (Fin (mu D) → ℤˣ) := sorry

/-- The complete character of an individual form. (Cox §3.B, Lemma 3.20.) -/
def formGenusVector (D : ℤ) (f : BinaryQF) : Fin (mu D) → ℤˣ := sorry

/-- The set of units of `ℤ/mℤ` represented by a form `f`. (Cox §3.B, Thm 3.21.) -/
def reprUnits (m : ℤ) (f : BinaryQF) : Set (ZMod m.natAbs)ˣ :=
  {u | ∃ x y : ℤ, (f.eval x y : ZMod m.natAbs) = (u : ZMod m.natAbs)}

/-- **Lemma 3.13** (Cox §3.B). The genus map `Φ : C(D) → {±1}^μ` is a group
homomorphism with respect to Dirichlet composition. -/
theorem lemma_3_13 (D : ℤ) (x y : FormClassGroup D) :
    genusVector D (compose D x y) = genusVector D x * genusVector D y := by
  sorry

/-- **Corollary 3.14(i)** (Cox §3.B). All genera of forms of discriminant `D`
consist of the same number of classes. -/
theorem cor_3_14_i (D : ℤ) (v w : Fin (mu D) → ℤˣ)
    (hv : ∃ a, genusVector D a = v) (hw : ∃ b, genusVector D b = w) :
    {x : FormClassGroup D | genusVector D x = v}.ncard
      = {x : FormClassGroup D | genusVector D x = w}.ncard := by
  sorry

/-- **Corollary 3.14(ii)** (Cox §3.B). The number of genera of forms of
discriminant `D` is a power of two. -/
theorem cor_3_14_ii (D : ℤ) : ∃ k : ℕ, (Set.range (genusVector D)).ncard = 2 ^ k := by
  sorry

/-- **Theorem 3.15(i)** (Cox §3.B). There are exactly `2^{μ−1}` genera of forms of
discriminant `D`, where `μ = mu D`. -/
theorem thm_3_15_i (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (Set.range (genusVector D)).ncard = 2 ^ (mu D - 1) := by
  sorry

/-- **Theorem 3.15(ii)** (Cox §3.B). The principal genus (the genus of the
principal class) is exactly the subgroup of squares `C(D)²`; every form in the
principal genus arises by duplication. -/
theorem thm_3_15_ii (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    {x : FormClassGroup D | genusVector D x = genusVector D (principalClass D)}
      = {x : FormClassGroup D | ∃ y : FormClassGroup D, compose D y y = x} := by
  sorry

/-- **Lemma 3.17** (Cox §3.B). The homomorphism `Ψ : (ℤ/Dℤ)ˣ → {±1}^μ` is
surjective and its kernel is the subgroup `H` of values represented by the
principal form; hence `(ℤ/Dℤ)ˣ / H ≅ {±1}^μ`. -/
theorem lemma_3_17 (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    Function.Surjective (Psi D) ∧
      ∀ u : (ZMod D.natAbs)ˣ, Psi D u = 1 ↔
        ∃ x y : ℤ, IsCoprime x y ∧
          ((principalForm D).eval x y : ZMod D.natAbs) = (u : ZMod D.natAbs) := by
  sorry

/-- **Lemma 3.20** (Cox §3.B). The complete character depends only on the form, and
two forms of discriminant `D` lie in the same genus iff they have the same complete
character. -/
theorem lemma_3_20 (D : ℤ) (f g : BinaryQF) (hf : f.discr = D) (hg : g.discr = D)
    (hfp : f.Primitive) (hgp : g.Primitive) :
    genus D f = genus D g ↔ formGenusVector D f = formGenusVector D g := by
  sorry

/-- **Theorem 3.21** (Cox §3.B), equivalence of conditions (i) and (ii). Two
primitive positive definite forms of discriminant `D < 0` are in the same genus
(represent the same values in `(ℤ/Dℤ)ˣ`) iff they represent the same values in
`(ℤ/mℤ)ˣ` for every nonzero `m`.

(Cox's full statement gives six equivalent conditions; the remaining
characterizations (iii)–(vi), via congruence/ `ℤ_p` / `ℚ`-equivalence, are deferred
— see ROADMAP.) -/
theorem thm_3_21 (D : ℤ) (hD : D < 0) (f g : BinaryQF) (hf : f.discr = D)
    (hg : g.discr = D) (hfp : f.Primitive) (hgp : g.Primitive)
    (hfa : 0 < f.a) (hga : 0 < g.a) :
    genus D f = genus D g ↔ ∀ m : ℤ, m ≠ 0 → reprUnits m f = reprUnits m g := by
  sorry

/-- **Theorem 3.22** (Cox §3.C). For `n > 0` the following are equivalent (the
fifth Cox condition, `C(−4n) ≅ (ℤ/2ℤ)^k`, is deferred — see ROADMAP):
* the genus map is injective (every genus is a single class);
* every reduced form of discriminant `−4n` has `b = 0`, `a = b`, or `a = c`;
* equivalence and proper equivalence coincide on forms of discriminant `−4n`;
* `h(−4n) = 2^{μ−1}`. -/
theorem thm_3_22 (n : ℕ) (hn : 0 < n) :
    [ Function.Injective (genusVector (-4 * (n : ℤ))),
      ∀ f : BinaryQF, f.discr = -4 * (n : ℤ) → f.Reduced →
        (f.b = 0 ∨ f.a = f.b ∨ f.a = f.c),
      ∀ f g : BinaryQF, f.discr = -4 * (n : ℤ) → g.discr = -4 * (n : ℤ) →
        (Equivalent f g ↔ ProperlyEquivalent f g),
      {f : BinaryQF | f.discr = -4 * (n : ℤ) ∧ f.Reduced ∧ f.Primitive}.ncard
        = 2 ^ (mu (-4 * (n : ℤ)) - 1) ].TFAE := by
  sorry

/-- **Euler's convenient (idoneal) number** (Cox §3.C). A positive integer `n` is
convenient if: whenever an odd `m` coprime to `n` is properly represented by
`x² + n y²` and `m = x² + n y²` has a unique solution with `x, y ≥ 0`, then `m` is
prime. -/
def ConvenientNumber (n : ℕ) : Prop :=
  ∀ m : ℕ, Odd m → Nat.Coprime m n →
    (∃ x y : ℤ, IsCoprime x y ∧ x ^ 2 + (n : ℤ) * y ^ 2 = (m : ℤ)) →
    (∃! q : ℕ × ℕ, (q.1 : ℤ) ^ 2 + (n : ℤ) * (q.2 : ℤ) ^ 2 = (m : ℤ)) →
    m.Prime

/-- **Proposition 3.24** (Cox §3.C). A positive integer `n` is convenient iff every
genus of forms of discriminant `−4n` consists of a single class. -/
theorem prop_3_24 (n : ℕ) (hn : 0 < n) :
    ConvenientNumber n ↔ Function.Injective (genusVector (-4 * (n : ℤ))) := by
  sorry

/-- **Lemma 3.25** (Cox §3.C). For odd `m` coprime to `n > 1`, the number of proper
representations of `m` by reduced forms of discriminant `−4n` is
`2 ∏_{p ∣ m} (1 + (−n/p))`.

(Deep: Cox proves this via the counting/genus argument of Exercise 3.20 — marked
`notready`.) -/
theorem lemma_3_25 (n m : ℕ) (hn : 1 < n) (hm : Odd m) (hco : Nat.Coprime m n) :
    ({p : BinaryQF × (ℤ × ℤ) |
        p.1.discr = -4 * (n : ℤ) ∧ p.1.Reduced ∧ p.1.Primitive ∧
        IsCoprime p.2.1 p.2.2 ∧ p.1.eval p.2.1 p.2.2 = (m : ℤ)}.ncard : ℤ)
      = 2 * ∏ q ∈ m.primeFactors, (1 + jacobiSym (-(n : ℤ)) q) := by
  sorry

/-- **Corollary 3.26** (Cox §3.C). If odd `m` coprime to `4n` (with `n > 1`) is
properly represented by a primitive form `f` of discriminant `−4n`, and `r` is the
number of prime divisors of `m`, then `m` is properly represented in exactly
`2^{r+1}` ways by a reduced form in the genus of `f`.

(Deep: follows from Lemma 3.25 — marked `notready`.) -/
theorem cor_3_26 (n m : ℕ) (hn : 1 < n) (hm : Odd m) (hco : Nat.Coprime m (4 * n))
    (f : BinaryQF) (hf : f.discr = -4 * (n : ℤ)) (hfp : f.Primitive) (hfa : 0 < f.a)
    (hrep : ∃ x y : ℤ, IsCoprime x y ∧ f.eval x y = (m : ℤ)) :
    {p : BinaryQF × (ℤ × ℤ) |
        p.1.discr = -4 * (n : ℤ) ∧ p.1.Reduced ∧ p.1.Primitive ∧
        genus (-4 * (n : ℤ)) p.1 = genus (-4 * (n : ℤ)) f ∧
        IsCoprime p.2.1 p.2.2 ∧ p.1.eval p.2.1 p.2.2 = (m : ℤ)}.ncard
      = 2 ^ (m.primeFactors.card + 1) := by
  sorry

end PrimesXNY2.Genera
