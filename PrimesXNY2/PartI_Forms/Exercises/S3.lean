/-
Copyright (c) 2026 Pragyan Manadhata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pragyan Manadhata
-/
import Mathlib
import PrimesXNY2.PartI_Forms.Genera

/-!
# Part I, §3 — Exercises (Cox, *Primes of the Form x² + ny²*, §3.E)

Faithful statements for the concrete, self-contained parts of Exercises 3.1–3.25.
Sub-parts that merely ask to *prove* a spine lemma, *complete a proof*, *enumerate*
forms of a given discriminant, or that need machinery not yet built (the
direct-composition predicate, `ℚ`/`ℤ_p`-equivalence, the abstract group structure
on `C(D)`, or the Kronecker symbol) are recorded as `\notready` blueprint nodes
only — see ROADMAP.

**Scaffold only:** every proof is `sorry`.
-/

namespace PrimesXNY2.PartI.S3

open PrimesXNY2.Forms PrimesXNY2.Genus PrimesXNY2.Genera

/-- **Exercise 3.1(a).** Gauss's coefficient formulas for a composition
`f(x,y) g(z,w) = F(a₁xz+b₁xw+c₁yz+d₁yw, a₂xz+b₂xw+c₂yz+d₂yw)`. -/
theorem ex_3_1_a (a b c a' b' c' A B C a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (h : ∀ x y z w : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2) * (a' * z ^ 2 + b' * z * w + c' * w ^ 2)
        = A * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w) ^ 2
          + B * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w)
              * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w)
          + C * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w) ^ 2) :
    a * a' = A * a₁ ^ 2 + B * a₁ * a₂ + C * a₂ ^ 2
      ∧ a * c' = A * b₁ ^ 2 + B * b₁ * b₂ + C * b₂ ^ 2
      ∧ a * b' = 2 * A * a₁ * b₁ + B * (a₁ * b₂ + a₂ * b₁) + 2 * C * a₂ * b₂ := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h 1 0 1 0
  · linear_combination h 1 0 0 1
  · linear_combination h 1 0 1 1 - h 1 0 1 0 - h 1 0 0 1

/-- **Exercise 3.1(b).** `a²(b'² − 4a'c') = (a₁b₂ − a₂b₁)²(B² − 4AC)`. -/
theorem ex_3_1_b (a b c a' b' c' A B C a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (h : ∀ x y z w : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2) * (a' * z ^ 2 + b' * z * w + c' * w ^ 2)
        = A * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w) ^ 2
          + B * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w)
              * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w)
          + C * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w) ^ 2) :
    a ^ 2 * (b' ^ 2 - 4 * a' * c') = (a₁ * b₂ - a₂ * b₁) ^ 2 * (B ^ 2 - 4 * A * C) := by
  sorry

/-- **Exercise 3.1(c).** `a' = ±(a₁c₂ − a₂c₁)`. -/
theorem ex_3_1_c (a b c a' b' c' A B C a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ)
    (h : ∀ x y z w : ℤ,
      (a * x ^ 2 + b * x * y + c * y ^ 2) * (a' * z ^ 2 + b' * z * w + c' * w ^ 2)
        = A * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w) ^ 2
          + B * (a₁ * x * z + b₁ * x * w + c₁ * y * z + d₁ * y * w)
              * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w)
          + C * (a₂ * x * z + b₂ * x * w + c₂ * y * z + d₂ * y * w) ^ 2) :
    a' = a₁ * c₂ - a₂ * c₁ ∨ a' = -(a₁ * c₂ - a₂ * c₁) := by
  sorry

/-- **Exercise 3.5(b).** With `X = xz − Cyw` and `Y = axw + a'yz + Byw`,
`(a x²+B xy+a'C y²)(a' z²+B zw+a C w²) = a a' X² + B X Y + C Y²`. -/
theorem ex_3_5_b (a a' B C : ℤ) : ∀ x y z w : ℤ,
    (a * x ^ 2 + B * x * y + a' * C * y ^ 2) * (a' * z ^ 2 + B * z * w + a * C * w ^ 2)
      = a * a' * (x * z - C * y * w) ^ 2
        + B * (x * z - C * y * w) * (a * x * w + a' * y * z + B * y * w)
        + C * (a * x * w + a' * y * z + B * y * w) ^ 2 := by
  intro x y z w
  ring

/-- **Exercise 3.5(e).** The Dirichlet composition of two primitive forms is
primitive. -/
theorem ex_3_5_e (f g : BinaryQF) (hfp : f.Primitive) (hgp : g.Primitive)
    (hcop : Int.gcd (Int.gcd f.a g.a) ((f.b + g.b) / 2) = 1) :
    (dirichletForm f g).Primitive := by
  sorry

/-- **Exercise 3.7.** `a c x² + b x y + y²` is properly equivalent to the principal
form of its discriminant. -/
theorem ex_3_7 (a b c : ℤ) :
    ProperlyEquivalent (⟨a * c, b, 1⟩ : BinaryQF)
      (principalForm ((⟨a * c, b, 1⟩ : BinaryQF).discr)) := by
  sorry

/-- **Exercise 3.8(a).** The Lagrangian (full-equivalence) class of `f` is the union
of the proper class of `f` and the proper class of its opposite. -/
theorem ex_3_8_a (f : BinaryQF) :
    {g : BinaryQF | Equivalent f g}
      = {g : BinaryQF | ProperlyEquivalent f g}
        ∪ {g : BinaryQF | ProperlyEquivalent f.opposite g} := by
  sorry

/-- **Exercise 3.8(b).** Equivalence of: the Lagrangian class equals the proper
class; `f` is properly equivalent to its opposite; `f` is (properly and) improperly
equivalent to itself. (Cox's fourth condition — class order `≤ 2` — is deferred.) -/
theorem ex_3_8_b (f : BinaryQF) :
    [ {g : BinaryQF | Equivalent f g} = {g : BinaryQF | ProperlyEquivalent f g},
      ProperlyEquivalent f f.opposite,
      ∃ M : Matrix (Fin 2) (Fin 2) ℤ, M.det = -1 ∧ action M f = f ].TFAE := by
  sorry

/-- **Exercise 3.12(b).** The number of genera of forms of a negative discriminant
`D` is at most `2^{μ−1}` (the bound preceding the equality of Theorem 3.15). -/
theorem ex_3_12_b (D : ℤ) (hD : D < 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (Set.range (genusVector D)).ncard ≤ 2 ^ (mu D - 1) := by
  sorry

/-- **Exercise 3.13(e).** Gauss's derivation of the second supplement:
`(2/p) = (−1)^{(p²−1)/8}`, i.e. `+1` iff `p ≡ ±1 (mod 8)`. -/
theorem ex_3_13_e (p : ℕ) [Fact p.Prime] (hodd : Odd p) :
    legendreSym p 2 = if p % 8 = 1 ∨ p % 8 = 7 then (1 : ℤ) else -1 := by
  have h2 : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hodd
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  rw [legendreSym.at_two h2, ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ p % 2 = 0)]

/-- **Exercise 3.16.** `x² + 18y²` and `2x² + 9y²` have the same discriminant `−72`
but lie in different genera (so genus is not a rational-equivalence invariant). -/
theorem ex_3_16 :
    (⟨1, 0, 18⟩ : BinaryQF).discr = (⟨2, 0, 9⟩ : BinaryQF).discr
      ∧ genus (-72) (⟨1, 0, 18⟩ : BinaryQF) ≠ genus (-72) (⟨2, 0, 9⟩ : BinaryQF) := by
  sorry

/-- **Exercise 3.20(a).** For odd `m` coprime to `n`, the number of solutions of
`x² ≡ −n (mod m)` is `∏_{p ∣ m} (1 + (−n/p))`. -/
theorem ex_3_20_a (n m : ℕ) [NeZero m] (hn : 0 < n) (hm : Odd m) (hco : Nat.Coprime m n) :
    ((Finset.univ.filter (fun x : ZMod m => x ^ 2 = ((-(n : ℤ) : ℤ) : ZMod m))).card : ℤ)
      = ∏ p ∈ m.primeFactors, (1 + jacobiSym (-(n : ℤ)) p) := by
  sorry

/-- **Exercise 3.21(b).** If `m = a² + 2b²` then
`m³ = (a³ − 6ab²)² + 2(3a²b − 2b³)²` (norm-cubing in `ℤ[√−2]`). -/
theorem ex_3_21_b (a b : ℤ) :
    (a ^ 2 + 2 * b ^ 2) ^ 3
      = (a ^ 3 - 6 * a * b ^ 2) ^ 2 + 2 * (3 * a ^ 2 * b - 2 * b ^ 3) ^ 2 := by
  ring

/-- **Exercise 3.21(c).** The cubing map `(a,b) ↦ (a³ − 6ab², 3a²b − 2b³)` on
`ℤ[√−2]` is injective. -/
theorem ex_3_21_c :
    Function.Injective
      (fun p : ℤ × ℤ => (p.1 ^ 3 - 6 * p.1 * p.2 ^ 2, 3 * p.1 ^ 2 * p.2 - 2 * p.2 ^ 3)) := by
  sorry

/-- **Exercise 3.22.** Fermat's result: the only integer solutions of `x³ = y² + 2`
are `(x, y) = (3, ±5)`. -/
theorem ex_3_22 (x y : ℤ) (h : x ^ 3 = y ^ 2 + 2) : x = 3 ∧ (y = 5 ∨ y = -5) := by
  sorry

/-- **Exercise 3.23.** An odd prime `p` of the form `x² + n y²` (`n > 1`) has a
unique representation `p = x² + n y²` with `x, y ≥ 0`. -/
theorem ex_3_23 (n p : ℕ) (hn : 1 < n) (hp : p.Prime) (hodd : Odd p)
    (hrep : ∃ x y : ℤ, x ^ 2 + (n : ℤ) * y ^ 2 = (p : ℤ)) :
    ∃! q : ℕ × ℕ, (q.1 : ℤ) ^ 2 + (n : ℤ) * (q.2 : ℤ) ^ 2 = (p : ℤ) := by
  sorry

end PrimesXNY2.PartI.S3
